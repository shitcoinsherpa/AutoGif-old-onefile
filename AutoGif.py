"""
AutoGIF - Advanced YouTube to GIF Converter
Creates high-quality GIFs from YouTube videos with AI-powered subtitles
"""
import sys
import time
import traceback
import subprocess
import os
from enum import Enum, auto
from pathlib import Path
import yt_dlp
import whisper
from PIL import Image, ImageDraw, ImageFont, ImageColor, ImageEnhance, ImageTk
import imageio
import tempfile
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import threading
import re
import cv2
from datetime import datetime
import logging
import json
from typing import Optional, Dict, Any, List, Tuple
import urllib.parse
from dataclasses import dataclass, asdict, field
import platform
import random
import math
import numpy as np

VERSION = "1.0.0"

# Configure logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('autogif_debug.log'),
        logging.StreamHandler()
    ]
)

@dataclass
class VideoSegment:
    start_time: float
    end_time: float
    text: str

@dataclass
class TextEffect:
    name: str
    enabled: bool = False
    intensity: int = 50  # 0-100 scale for effect strength

@dataclass
class FrameTiming:
    frame_index: int
    duration: float  # in seconds

@dataclass
class MotionRegion:
    x1: int
    y1: int
    x2: int
    y2: int
    enabled: bool = True
    fade_edges: bool = True

@dataclass
class OptimizationSettings:
    # Frame timing
    frame_timings: List[FrameTiming] = field(default_factory=list)
    default_duration: float = 0.1  # 100ms default
    pause_duration: float = 1.0    # 1s for freeze frames
    fast_duration: float = 0.05    # 50ms for quick frames
    
    # Motion detection
    detect_static_frames: bool = True
    static_threshold: float = 0.98
    motion_regions: List[MotionRegion] = field(default_factory=list)
    
    # Color and dithering
    dither_mode: str = "FLOYDSTEINBERG"  # NONE, ORDERED, FLOYDSTEINBERG
    color_limit: int = 0  # 0 means use source colors
    web_safe_colors: bool = False
    custom_palette: Optional[List[str]] = None
    
@dataclass
class TextEffectSettings:
    shake: TextEffect = field(default_factory=lambda: TextEffect("Shake"))
    bounce: TextEffect = field(default_factory=lambda: TextEffect("Bounce"))
    slide: TextEffect = field(default_factory=lambda: TextEffect("Slide"))
    fade: TextEffect = field(default_factory=lambda: TextEffect("Fade"))
    typewriter: TextEffect = field(default_factory=lambda: TextEffect("Typewriter"))
    wave: TextEffect = field(default_factory=lambda: TextEffect("Wave"))
    glow: TextEffect = field(default_factory=lambda: TextEffect("Glow"))
    neon: TextEffect = field(default_factory=lambda: TextEffect("Neon"))
    rainbow: TextEffect = field(default_factory=lambda: TextEffect("Rainbow"))
    metallic: TextEffect = field(default_factory=lambda: TextEffect("Metallic"))
    depth_3d: TextEffect = field(default_factory=lambda: TextEffect("3D Depth"))

class EffectLayer(Enum):
    """Defines rendering order for effect layers"""
    BACKGROUND = auto()  # Glow, shadow effects
    BASE = auto()        # Main text, outline
    OVERLAY = auto()     # Rainbow, neon effects

@dataclass
class EffectState:
    """Stores the current state of all text effects for a frame"""
    position: Tuple[float, float] = (0, 0)  # (x, y) offset
    alpha: float = 1.0  # Global alpha/opacity
    color: Optional[Tuple[int, int, int]] = None  # RGB color override
    glow_radius: float = 0.0  # Radius for glow effect
    glow_color: Optional[Tuple[int, int, int]] = None  # Glow color
    outline_width: int = 2  # Width of text outline
    outline_color: Optional[Tuple[int, int, int]] = None  # Outline color
    typewriter_progress: float = 1.0  # Progress for typewriter effect (0-1)
    wave_offset: float = 0.0  # Y-offset for wave effect
    neon_offsets: List[float] = field(default_factory=list)  # X-offsets for neon effect
    metallic_colors: List[Tuple[int, int, int]] = field(default_factory=list)  # Colors for metallic effect
    transform_matrix: Optional[np.ndarray] = None  # For advanced transformations

@dataclass 
class EffectTiming:
    """Controls timing parameters for animated effects"""
    frame_num: int
    total_frames: int
    base_speed: float = 1.0
    bounce_freq: float = 0.2
    wave_freq: float = 0.2
    slide_freq: float = 0.1
    fade_freq: float = 0.1
    neon_freq: float = 0.1
    metallic_speed: float = 0.5

class EffectManager:
    """Manages text effect lifecycle and coordinates effect interactions with improved resource management"""
    
    def __init__(self, config: 'ConfigManager'):
        self.config = config
        self.font = None
        self._load_font()
        self.frame_size: Optional[Tuple[int, int]] = None
        self.current_state: Optional[EffectState] = None
        self._temp_resources: List[Any] = []
        self.random = random.Random()
        # Enhanced caching system
        self._effect_cache: Dict[str, Any] = {}
        self._canvas_cache: Dict[str, Image.Image] = {}
        self._max_cache_size = 50
        # Performance monitoring
        self._render_times: List[float] = []
        self._max_render_times = 100
        
    def _load_font(self):
        """Load font with error handling and fallbacks"""
        try:
            font_name = self.config.settings.font_name
            font_size = self.config.settings.font_size
        
            # Try loading from Windows Fonts directory first
            if platform.system() == "Windows":
                # Map common font names to their actual filenames
                font_files = {
                    'Arial': 'arial.ttf',
                    'Times New Roman': 'times.ttf',
                    'Impact': 'impact.ttf',
                    'Bahnschrift': 'bahnschrift.ttf',
                    'Georgia': 'georgia.ttf',
                    'Calibri': 'calibri.ttf',
                    'Tahoma': 'tahoma.ttf',
                    'Verdana': 'verdana.ttf',
                    'Segoe UI': 'segoeui.ttf',
                    'Trebuchet MS': 'trebuc.ttf'
                }
            
                # Get correct filename for the requested font
                font_file = font_files.get(font_name, font_name.lower() + '.ttf')
                font_path = Path("C:/Windows/Fonts") / font_file
            
                if font_path.exists():
                    try:
                        self.font = ImageFont.truetype(str(font_path), font_size)
                        logging.debug(f"Successfully loaded system font: {font_name}")
                        return
                    except Exception as e:
                        logging.warning(f"Could not load system font {font_name}: {e}")
                    
            # Try loading directly by name (for non-Windows systems)
            try:
                self.font = ImageFont.truetype(font_name, font_size)
                logging.debug(f"Successfully loaded font: {font_name}")
                return
            except Exception as e:
                logging.warning(f"Could not load system font {font_name}: {e}")
        
            # Try Arial as fallback
            try:
                self.font = ImageFont.truetype("arial.ttf", font_size)
                logging.debug("Using Arial as fallback font")
                return
            except:
                pass
            
            # Last resort: default font
            self.font = ImageFont.load_default()
            logging.warning("Using default font as fallback")
        
        except Exception as e:
            logging.error(f"Font loading error: {e}")
            self.font = ImageFont.load_default()
            
    def _wrap_text(self, text: str, max_width: int) -> List[str]:
        """Wrap text to fit within max_width pixels with improved boundary handling"""
        # Use more width of the frame (90% instead of 80%)
        safe_max_width = int(max_width * 0.9)

        # Calculate maximum height (70% of frame height to ensure text stays within bounds)
        max_height = int(self.frame_size[1] * 0.7)
        line_spacing = int(self.font.size * 1.2)
        max_lines = max_height // line_spacing

        # Handle empty or None text
        if not text:
            return []
    
        # Split into words and handle newlines
        lines = []
        current_line = []
        current_width = 0

        # Performance optimization: Pre-calculate space width
        space_width = self.font.getbbox(' ')[2]

        # Split text into paragraphs first (handle explicit line breaks)
        paragraphs = text.split('\n')

        for paragraph in paragraphs:
            words = paragraph.split()
    
            if not words:
                lines.append('')
                continue
            
            # Performance optimization: Pre-calculate word dimensions
            word_dimensions = {}
            for word in words:
                if word:
                    word_bbox = self.font.getbbox(word + ' ')
                    word_dimensions[word] = word_bbox[2] - word_bbox[0]
        
            for word in words:
                # Skip empty words
                if not word:
                    continue
            
                # Get cached word dimensions
                word_width = word_dimensions[word]
        
                # Handle long words that need to be broken
                if word_width > safe_max_width:
                    # Add current line if it exists
                    if current_line:
                        lines.append(' '.join(current_line))
                        if len(lines) >= max_lines:
                            break
                        current_line = []
                        current_width = 0
            
                    # Break the word into parts
                    chars = list(word)
                    part = ''
                    part_width = 0
            
                    for i, char in enumerate(chars):
                        char_bbox = self.font.getbbox(char)
                        char_width = char_bbox[2] - char_bbox[0]
                
                        if part_width + char_width <= safe_max_width:
                            part += char
                            part_width += char_width
                        else:
                            if part:
                                # Only add hyphen if this isn't the last part
                                if i < len(chars) - 1:
                                    lines.append(part + '-')
                                else:
                                    lines.append(part)
                                if len(lines) >= max_lines:
                                    break
                            part = char
                            part_width = char_width
            
                    if part and len(lines) < max_lines:
                        current_line = [part]
                        current_width = part_width
                    continue
        
                # Calculate width with proper spacing
                new_width = current_width + word_width
                if current_line:  # Add space width if not first word
                    new_width += space_width
        
                # Check if adding this word would exceed the line width
                if new_width <= safe_max_width:
                    current_line.append(word)
                    current_width = new_width
                else:
                    # Add the current line and start a new one
                    if current_line:
                        lines.append(' '.join(current_line))
                        if len(lines) >= max_lines:
                            break
                    current_line = [word]
                    current_width = word_width
    
            # Add the last line of the paragraph if there is one
            if current_line and len(lines) < max_lines:
                lines.append(' '.join(current_line))
                current_line = []
                current_width = 0

        # Handle case where text is too long
        if len(lines) > max_lines:
            # Keep max_lines - 1 lines and add ellipsis to last line
            lines = lines[:max_lines-1]
            last_line = lines[-1]
    
            # Cache ellipsis width
            ellipsis_width = self.font.getbbox('...')[2]
    
            # Ensure the last line with ellipsis fits
            while last_line and self.font.getbbox(last_line)[2] + ellipsis_width > safe_max_width:
                last_line = ' '.join(last_line.split()[:-1])
                if not last_line:
                    break
    
            if last_line:
                lines[-1] = last_line + '...'
            else:
                # If we can't fit even one word with ellipsis, just use ellipsis
                lines[-1] = '...'

        # Final verification pass with performance optimizations
        final_lines = []
        line_measurements = {}  # Cache line measurements
        
        for line in lines:
            if not line:  # Preserve empty lines
                final_lines.append(line)
                continue
        
            # Use cached measurements if available
            if line in line_measurements:
                line_width = line_measurements[line]
            else:
                line_bbox = self.font.getbbox(line)
                if not line_bbox:  # Skip invalid measurements
                    continue
                line_width = line_bbox[2] - line_bbox[0]
                line_measurements[line] = line_width
    
            if line_width > safe_max_width:
                # Emergency break for any remaining long lines
                words = line.split()
                temp_line = []
                temp_width = 0
        
                for word in words:
                    word_bbox = self.font.getbbox(word + ' ')
                    word_width = word_bbox[2] - word_bbox[0]
            
                    new_width = temp_width + word_width
                    if temp_line:  # Add space width if not first word
                        new_width += space_width
            
                    if new_width <= safe_max_width:
                        temp_line.append(word)
                        temp_width = new_width
                    else:
                        if temp_line:
                            final_lines.append(' '.join(temp_line))
                            if len(final_lines) >= max_lines:
                                break
                        temp_line = [word]
                        temp_width = word_width
        
                if temp_line and len(final_lines) < max_lines:
                    final_lines.append(' '.join(temp_line))
            else:
                if len(final_lines) < max_lines:
                    final_lines.append(line)

        # Final safety check for vertical bounds
        if len(final_lines) > max_lines:
            final_lines = final_lines[:max_lines-1]
            last_line = final_lines[-1]
            
            # Use cached ellipsis width
            while last_line and self.font.getbbox(last_line)[2] + ellipsis_width > safe_max_width:
                last_line = ' '.join(last_line.split()[:-1])
                if not last_line:
                    break
                    
            final_lines[-1] = (last_line + '...') if last_line else '...'

        # Ensure we're not returning empty list
        if not final_lines:
            final_lines = ['...']

        return final_lines

    def prepare_frame(self, frame: Image.Image, frame_num: int, total_frames: int) -> None:
        """Initialize effect state for new frame with improved caching and performance monitoring"""
        start_time = time.perf_counter()
        
        try:
            self.frame_size = frame.size
            timing = EffectTiming(frame_num, total_frames)
            
            # Generate cache key based on frame parameters and active effects
            settings = self.config.settings.text_effects
            cache_key = f"{frame_num}_{total_frames}_{hash(frozenset({
                k: getattr(settings, k).enabled 
                for k in vars(settings) 
                if isinstance(getattr(settings, k), TextEffect)
            }.items()))}"
            
            # Check if we have cached state
            if cache_key in self._effect_cache:
                self.current_state = self._effect_cache[cache_key]
                return
                
            self.current_state = self._calculate_effect_state(timing)
            
            # Cache the state if it's worth caching (complex effects enabled)
            if self._should_cache_state():
                self._effect_cache[cache_key] = self.current_state
                
                # Maintain cache size with LRU policy
                if len(self._effect_cache) > self._max_cache_size:
                    oldest_keys = sorted(self._effect_cache.keys())[:len(self._effect_cache) - self._max_cache_size]
                    for key in oldest_keys:
                        del self._effect_cache[key]
        
        finally:
            # Record performance metrics
            elapsed = time.perf_counter() - start_time
            self._render_times.append(elapsed)
            if len(self._render_times) > self._max_render_times:
                self._render_times.pop(0)
            
            # Log performance warning if preparation takes too long
            if elapsed > 0.1:  # 100ms threshold
                logging.warning(f"Frame preparation took {elapsed:.3f}s")

    def _should_cache_state(self) -> bool:
        """Determine if current state should be cached based on active effects and complexity"""
        settings = self.config.settings.text_effects
        
        # Count active complex effects
        complex_effects = sum(1 for effect in [
            settings.rainbow,
            settings.neon,
            settings.metallic,
            settings.depth_3d,
            settings.wave
        ] if effect.enabled)
        
        # Cache if multiple complex effects are active or if any high-intensity effects are enabled
        return complex_effects > 1 or any(
            effect.enabled and effect.intensity > 75
            for effect in [settings.rainbow, settings.neon, settings.metallic]
        )

    def _calculate_effect_state(self, timing: EffectTiming) -> EffectState:
        """Calculate combined effect parameters for current frame with enhanced stability"""
        state = EffectState()
        state.frame_num = timing.frame_num
        state.total_frames = timing.total_frames
        settings = self.config.settings.text_effects
    
        # Set frame-specific random seed for deterministic effects
        self.random.seed(timing.frame_num * 12345)
    
        try:
            # Calculate positional offsets with improved stability
            offset_x = offset_y = 0
        
            if settings.shake.enabled:
                shake_amount = (settings.shake.intensity / 100.0) * 10
                # Use triangular distribution for more natural movement
                offset_x += self.random.triangular(-shake_amount, shake_amount)
                offset_y += self.random.triangular(-shake_amount, shake_amount)
            
            if settings.bounce.enabled:
                bounce_amount = (settings.bounce.intensity / 100.0) * 20
                bounce_freq = timing.bounce_freq * (settings.bounce.intensity / 100.0)
                # Add smoothing to bounce effect
                offset_y += math.sin(timing.frame_num * bounce_freq) * bounce_amount
                # Add subtle horizontal movement for more natural effect
                offset_x += math.sin(timing.frame_num * bounce_freq * 0.5) * (bounce_amount * 0.15)
            
            if settings.slide.enabled:
                slide_amount = (settings.slide.intensity / 100.0) * 30
                slide_freq = timing.slide_freq * (settings.slide.intensity / 100.0)
                # Add easing to slide effect
                slide_progress = (math.sin(timing.frame_num * slide_freq) + 1) / 2
                offset_x += self._ease_in_out(slide_progress) * slide_amount
            
            # Ensure offsets stay within reasonable bounds
            max_offset = min(self.frame_size[0], self.frame_size[1]) * 0.1  # 10% of frame size
            offset_x = max(min(offset_x, max_offset), -max_offset)
            offset_y = max(min(offset_y, max_offset), -max_offset)
            
            state.position = (offset_x, offset_y)
        
            # Calculate alpha/opacity with smoother transitions
            if settings.fade.enabled:
                fade_intensity = (settings.fade.intensity / 100.0)
                fade_cycle = (math.sin(timing.frame_num * timing.fade_freq) + 1) / 2
                # Add easing for smoother fade transitions
                fade_progress = self._ease_in_out(fade_cycle)
                state.alpha = max(0.3, 1 - fade_intensity + fade_intensity * fade_progress)
        
            # Set effect colors and properties with enhanced color handling
            if settings.glow.enabled:
                state.glow_radius = (settings.glow.intensity / 100.0) * 20
                # Parse and validate glow color
                try:
                    state.glow_color = self._parse_color(self.config.settings.font_color)
                except ValueError:
                    state.glow_color = (255, 255, 255)  # Fallback to white
            
            if settings.neon.enabled:
                state.neon_offsets = []
                neon_intensity = settings.neon.intensity / 100.0
                # Calculate smooth neon offsets
                for i in range(3):
                    phase = timing.frame_num * timing.neon_freq + i * 2.094
                    offset = math.sin(phase) * neon_intensity * 5
                    # Add subtle variation to each color layer
                    variation = math.cos(phase * 0.5) * neon_intensity
                    state.neon_offsets.append(offset + variation)
                
            if settings.metallic.enabled:
                metallic_intensity = settings.metallic.intensity / 100.0
                base_hue = (timing.frame_num * timing.metallic_speed) % 360
                # Generate smoother metallic color transitions
                state.metallic_colors = [
                    self._hsv_to_rgb(
                        (base_hue + i * 30 + math.sin(timing.frame_num * 0.1) * 10) % 360,
                        0.8,
                        1.0
                    ) for i in range(3)
                ]
        
            # Set outline properties with validation
            state.outline_width = max(1, min(
                self.config.settings.outline_width,
                min(self.frame_size) // 20  # Cap at 5% of smaller frame dimension
            ))
            try:
                state.outline_color = self._parse_color(self.config.settings.outline_color)
            except ValueError:
                state.outline_color = (0, 0, 0)  # Fallback to black
        
            # Set typewriter progress with smoothing
            if settings.typewriter.enabled:
                raw_progress = timing.frame_num / (timing.total_frames * 0.5)
                state.typewriter_progress = self._ease_in_out(min(1.0, raw_progress))
        
            # Set wave offset with improved animation
            if settings.wave.enabled:
                wave_intensity = settings.wave.intensity / 100.0
                base_offset = math.sin(timing.frame_num * timing.wave_freq)
                # Add secondary wave for more interesting movement
                secondary = math.sin(timing.frame_num * timing.wave_freq * 0.5) * 0.3
                state.wave_offset = (base_offset + secondary) * (20 * wave_intensity)
        
            # Set 3D depth transform with improved perspective
            if settings.depth_3d.enabled:
                depth_intensity = settings.depth_3d.intensity / 100.0
                # Add subtle rotation around all axes for more dynamic effect
                angle_x = math.sin(timing.frame_num * 0.1) * (math.pi / 8 * depth_intensity)
                angle_y = math.cos(timing.frame_num * 0.08) * (math.pi / 12 * depth_intensity)
                angle_z = math.sin(timing.frame_num * 0.05) * (math.pi / 16 * depth_intensity)
                
                # Create combined transformation matrix
                transform = np.array([
                    [math.cos(angle_y) * math.cos(angle_z), -math.cos(angle_y) * math.sin(angle_z), math.sin(angle_y)],
                    [math.cos(angle_x) * math.sin(angle_z), math.cos(angle_x) * math.cos(angle_z), -math.sin(angle_x)],
                    [-math.sin(angle_y), math.sin(angle_x) * math.cos(angle_y), math.cos(angle_x) * math.cos(angle_y)]
                ])
                state.transform_matrix = transform
        
            return state

        except Exception as e:
            logging.error(f"Error calculating effect state: {e}")
            traceback.print_exc()
            # Return a safe default state
            return EffectState(
                frame_num=timing.frame_num,
                total_frames=timing.total_frames,
                position=(0, 0),
                alpha=1.0
            )

    def _parse_color(self, color_str: str) -> Tuple[int, int, int]:
        """Parse color string with enhanced validation and error handling"""
        try:
            # Handle hex colors
            if color_str.startswith('#'):
                color_str = color_str.lstrip('#')
                if len(color_str) == 3:
                    color_str = ''.join(c + c for c in color_str)
                return tuple(int(color_str[i:i+2], 16) for i in (0, 2, 4))
            
            # Handle rgb() format
            if color_str.startswith('rgb'):
                values = color_str.strip('rgb()').split(',')
                return tuple(max(0, min(255, int(v.strip()))) for v in values)
            
            # Handle named colors (limited set for performance)
            color_map = {
                'white': (255, 255, 255),
                'black': (0, 0, 0),
                'red': (255, 0, 0),
                'green': (0, 255, 0),
                'blue': (0, 0, 255),
                'yellow': (255, 255, 0),
                'purple': (128, 0, 128),
                'orange': (255, 165, 0)
            }
            if color_str.lower() in color_map:
                return color_map[color_str.lower()]
            
            raise ValueError(f"Invalid color format: {color_str}")
            
        except Exception as e:
            logging.warning(f"Color parsing error: {e}")
            raise ValueError(f"Invalid color: {color_str}")

    def _ease_in_out(self, t: float) -> float:
        """Smooth easing function for animations"""
        # Clamp input to 0-1 range
        t = max(0.0, min(1.0, t))
        # Cubic easing
        if t < 0.5:
            return 4 * t * t * t
        else:
            return 1 - pow(-2 * t + 2, 3) / 2

    def _hsv_to_rgb(self, h: float, s: float, v: float) -> Tuple[int, int, int]:
        """Convert HSV color values to RGB with improved accuracy and validation"""
        try:
            h = float(h) % 360
            s = max(0.0, min(1.0, float(s)))
            v = max(0.0, min(1.0, float(v)))
            
            h60 = h / 60.0
            h60f = math.floor(h60)
            hi = int(h60f) % 6
            f = h60 - h60f
            p = v * (1 - s)
            q = v * (1 - f * s)
            t = v * (1 - (1 - f) * s)
            
            r, g, b = 0, 0, 0
            if hi == 0: r, g, b = v, t, p
            elif hi == 1: r, g, b = q, v, p
            elif hi == 2: r, g, b = p, v, t
            elif hi == 3: r, g, b = p, q, v
            elif hi == 4: r, g, b = t, p, v
            elif hi == 5: r, g, b = v, p, q
            
            # Ensure valid RGB values
            return (
                max(0, min(255, int(r * 255))),
                max(0, min(255, int(g * 255))),
                max(0, min(255, int(b * 255)))
            )
            
        except Exception as e:
            logging.error(f"HSV to RGB conversion error: {e}")
            return (255, 255, 255)  # Return white as fallback

    def _make_hashable(self, obj):
        """Convert a potentially unhashable object into a hashable form"""
        if isinstance(obj, (list, tuple)):
            return tuple(self._make_hashable(x) for x in obj)
        elif isinstance(obj, dict):
            return tuple(sorted((k, self._make_hashable(v)) for k, v in obj.items()))
        elif isinstance(obj, (int, float, str, bool, type(None))):
            return obj
        # For numpy arrays (like transform_matrix)
        elif hasattr(obj, 'tolist'):
            return self._make_hashable(obj.tolist())
        return str(obj)

    def render_text(self, frame: Image.Image, text: str, base_position: Tuple[int, int]) -> Image.Image:
        """Render text with all active effects with improved performance and quality"""
        start_time = time.perf_counter()
        
        try:
            if not self.current_state:
                return frame

            # Create a simpler cache key using just the essential state values
            cache_key = f"{text}_{self.current_state.frame_num}_{self.current_state.position}_{self.current_state.alpha}"
            
            # Check render cache
            if cache_key in self._canvas_cache:
                result = Image.alpha_composite(frame.convert('RGBA'), self._canvas_cache[cache_key])
                logging.debug(f"Cache hit for render: {cache_key}")
                return result

            # Create a single transparent layer for all text effects
            text_layer = Image.new('RGBA', frame.size, (0, 0, 0, 0))
            self._temp_resources.append(text_layer)

            # Calculate maximum width for text wrapping (90% of frame width)
            max_width = int(frame.size[0] * 0.9)
        
            # Wrap text with caching
            lines = self._wrap_text(text, max_width)
        
            # Calculate total height of wrapped text
            line_spacing = int(self.font.size * 1.2)  # 120% of font size
            total_height = len(lines) * line_spacing
        
            # Calculate safe margins
            bottom_margin = int(frame.size[1] * 0.1)  # 10% margin from bottom
        
            # Calculate vertical position to ensure text stays within bounds
            base_y = frame.size[1] - bottom_margin - total_height

            settings = self.config.settings.text_effects
            draw = ImageDraw.Draw(text_layer)

            # Create effect layers with proper resource management
            effect_layers = []
            
            try:
                # Create separate layers for each effect category
                bg_layer = Image.new('RGBA', frame.size, (0, 0, 0, 0))
                main_layer = Image.new('RGBA', frame.size, (0, 0, 0, 0))
                overlay_layer = Image.new('RGBA', frame.size, (0, 0, 0, 0))
                effect_layers.extend([bg_layer, main_layer, overlay_layer])

                # Process each line with optimized rendering
                for line_idx, line in enumerate(lines):
                    current_y = base_y + (line_idx * line_spacing)
                    
                    # Cache line measurements
                    line_bbox = self.font.getbbox(line)
                    if not line_bbox:
                        continue
                        
                    line_width = line_bbox[2] - line_bbox[0]
                    line_x = (frame.size[0] - line_width) // 2  # Center each line

                    # Apply 3D depth effect first (background layer)
                    if settings.depth_3d.enabled:
                        self._apply_3d_depth_effect(
                            draw=ImageDraw.Draw(bg_layer),
                            line=line,
                            base_x=line_x,
                            base_y=current_y,
                            intensity=settings.depth_3d.intensity
                        )

                    # Apply glow effect (background layer)
                    if settings.glow.enabled:
                        self._apply_glow_effect(
                            draw=ImageDraw.Draw(bg_layer),
                            line=line,
                            base_x=line_x,
                            base_y=current_y,
                            intensity=settings.glow.intensity
                        )

                    # Calculate effect position adjustments with smoothing
                    pos_x = line_x
                    pos_y = current_y

                    if settings.shake.enabled:
                        shake_offset = self._calculate_shake_offset(settings.shake.intensity)
                        pos_x += shake_offset[0]
                        pos_y += shake_offset[1]

                    if settings.bounce.enabled:
                        bounce_offset = self._calculate_bounce_offset(settings.bounce.intensity)
                        pos_x += bounce_offset[0]
                        pos_y += bounce_offset[1]

                    if settings.slide.enabled:
                        slide_offset = self._calculate_slide_offset(settings.slide.intensity)
                        pos_x += slide_offset[0]
                        pos_y += slide_offset[1]

                    # Apply wave effect with optimized rendering
                    if settings.wave.enabled:
                        self._apply_wave_effect(
                            draw=ImageDraw.Draw(main_layer),
                            line=line,
                            base_x=pos_x,
                            base_y=pos_y,
                            intensity=settings.wave.intensity
                        )
                        continue  # Skip main text drawing for wave effect

                    # Draw outline with improved quality
                    self._apply_outline(
                        draw=ImageDraw.Draw(main_layer),
                        line=line,
                        pos_x=pos_x,
                        pos_y=pos_y,
                        width=self.config.settings.outline_width,
                        color=ImageColor.getrgb(self.config.settings.outline_color)
                    )

                    # Calculate alpha for fade effect with smoother transitions
                    alpha = 255
                    if settings.fade.enabled:
                        alpha = self._calculate_fade_alpha(settings.fade.intensity)

                    # Draw main text with effects
                    if settings.rainbow.enabled:
                        self._apply_rainbow_effect(
                            draw=ImageDraw.Draw(overlay_layer),
                            line=line,
                            pos_x=pos_x,
                            pos_y=pos_y,
                            alpha=alpha
                        )
                    else:
                        font_color = ImageColor.getrgb(self.config.settings.font_color)
                        draw.text(
                            (pos_x, pos_y),
                            line,
                            font=self.font,
                            fill=(*font_color, alpha)
                        )

                    # Apply neon effect (overlay layer)
                    if settings.neon.enabled:
                        self._apply_neon_effect(
                            draw=ImageDraw.Draw(overlay_layer),
                            line=line,
                            pos_x=pos_x,
                            pos_y=pos_y,
                            intensity=settings.neon.intensity
                        )

                    # Apply metallic effect (overlay layer)
                    if settings.metallic.enabled:
                        self._apply_metallic_effect(
                            draw=ImageDraw.Draw(overlay_layer),
                            line=line,
                            pos_x=pos_x,
                            pos_y=pos_y,
                            intensity=settings.metallic.intensity
                        )

                # Apply typewriter effect last
                if settings.typewriter.enabled:
                    self._apply_typewriter_effect(text_layer, lines, base_y, line_spacing)

                # Composite all layers with proper alpha handling
                text_layer = self._composite_layers([bg_layer, main_layer, text_layer, overlay_layer])

                # Apply global opacity if specified
                if hasattr(self.config.settings, 'text_opacity'):
                    text_layer = self._apply_global_opacity(text_layer)

                # Cache the result if appropriate
                if self._should_cache_render(text_layer):
                    self._canvas_cache[cache_key] = text_layer.copy()
                    
                    # Maintain cache size
                    if len(self._canvas_cache) > self._max_cache_size:
                        oldest_keys = sorted(self._canvas_cache.keys())[:len(self._canvas_cache) - self._max_cache_size]
                        for key in oldest_keys:
                            del self._canvas_cache[key]

                # Final composition
                result = Image.alpha_composite(frame.convert('RGBA'), text_layer)

                # Performance monitoring
                render_time = time.perf_counter() - start_time
                if render_time > 0.1:  # Log slow renders
                    logging.warning(f"Slow text rendering: {render_time:.3f}s")
                
                return result

            finally:
                # Clean up effect layers
                for layer in effect_layers:
                    try:
                        layer.close()
                    except Exception as e:
                        logging.warning(f"Failed to close effect layer: {e}")

        except Exception as e:
            logging.error(f"Error rendering text effects: {e}")
            traceback.print_exc()
            return frame

    def _should_cache_render(self, rendered_layer: Image.Image) -> bool:
        """Determine if rendered layer should be cached based on complexity and memory usage"""
        # Check if complex effects are enabled
        settings = self.config.settings.text_effects
        has_complex_effects = any([
            settings.rainbow.enabled,
            settings.neon.enabled,
            settings.metallic.enabled,
            settings.depth_3d.enabled,
            settings.wave.enabled
        ])
        
        if not has_complex_effects:
            return False
            
        # Estimate memory usage
        try:
            mem_usage = rendered_layer.size[0] * rendered_layer.size[1] * 4  # RGBA
            max_mem = 100 * 1024 * 1024  # 100MB limit
            return mem_usage < max_mem
        except:
            return False

    def _composite_layers(self, layers: List[Image.Image]) -> Image.Image:
        """Composite multiple layers with proper alpha handling and error checking"""
        try:
            result = Image.new('RGBA', layers[0].size, (0, 0, 0, 0))
            for layer in layers:
                if layer.mode != 'RGBA':
                    layer = layer.convert('RGBA')
                try:
                    result = Image.alpha_composite(result, layer)
                except Exception as e:
                    logging.error(f"Layer composition error: {e}")
            return result
        except Exception as e:
            logging.error(f"Layer composition error: {e}")
            return layers[0].copy()

    def _apply_global_opacity(self, layer: Image.Image) -> Image.Image:
        """Apply global opacity to layer with proper alpha handling"""
        try:
            opacity = self.config.settings.text_opacity / 100.0
            if opacity >= 1.0:
                return layer
                
            if opacity <= 0.0:
                return Image.new('RGBA', layer.size, (0, 0, 0, 0))
                
            alpha = layer.split()[3]
            alpha = alpha.point(lambda x: int(x * opacity))
            layer.putalpha(alpha)
            return layer
        except Exception as e:
            logging.error(f"Opacity application error: {e}")
            return layer

    def _calculate_shake_offset(self, intensity: float) -> Tuple[float, float]:
        """Calculate shake effect offset with improved randomization"""
        try:
            shake_amount = (intensity / 100.0) * 15
            # Use triangular distribution for more natural movement
            return (
                self.random.triangular(-shake_amount, shake_amount),
                self.random.triangular(-shake_amount, shake_amount)
            )
        except Exception as e:
            logging.error(f"Shake calculation error: {e}")
            return (0, 0)

    def _calculate_bounce_offset(self, intensity: float) -> Tuple[float, float]:
        """Calculate bounce effect offset with improved motion"""
        try:
            bounce_amount = (intensity / 100.0) * 25
            frame_progress = self.current_state.frame_num / self.current_state.total_frames
            vertical = math.sin(frame_progress * math.pi * 2) * bounce_amount
            # Add subtle horizontal movement
            horizontal = math.sin(frame_progress * math.pi) * (bounce_amount * 0.2)
            return (horizontal, vertical)
        except Exception as e:
            logging.error(f"Bounce calculation error: {e}")
            return (0, 0)

    def _calculate_slide_offset(self, intensity: float) -> Tuple[float, float]:
        """Calculate slide effect offset with smooth easing"""
        try:
            slide_amount = (intensity / 100.0) * 40
            frame_progress = self.current_state.frame_num / self.current_state.total_frames
            # Apply easing for smoother motion
            eased_progress = self._ease_in_out(frame_progress)
            return (math.sin(eased_progress * math.pi * 2) * slide_amount, 0)
        except Exception as e:
            logging.error(f"Slide calculation error: {e}")
            return (0, 0)

    def _calculate_fade_alpha(self, intensity: float) -> int:
        """Calculate fade effect alpha with smooth transitions"""
        try:
            fade_intensity = (intensity / 100.0)
            frame_progress = self.current_state.frame_num / self.current_state.total_frames
            fade_cycle = (math.sin(frame_progress * math.pi * 2) + 1) / 2
            # Apply easing for smoother fades
            eased_fade = self._ease_in_out(fade_cycle)
            return int(255 * (1 - fade_intensity + fade_intensity * eased_fade))
        except Exception as e:
            logging.error(f"Fade alpha calculation error: {e}")
            return 255

    def _apply_3d_depth_effect(self, draw: ImageDraw.Draw, line: str, base_x: float, base_y: float, intensity: float) -> None:
        """Apply 3D depth effect with improved perspective and shadows"""
        try:
            depth_intensity = (intensity / 100.0) * 8
            max_layers = int(depth_intensity * 3)
            
            # Calculate shadow progression
            for i in range(max_layers):
                # Progressive offset calculation
                offset = i * 2
                
                # Calculate alpha with smooth falloff
                alpha = int(150 * (1 - (i / max_layers) ** 1.5))
                shadow_color = (0, 0, 0, alpha)
                
                # Apply perspective transformation
                perspective_x = base_x + offset * 1.2
                perspective_y = base_y + offset
                
                # Draw shadow layer with anti-aliasing
                draw.text(
                    (perspective_x, perspective_y),
                    line,
                    font=self.font,
                    fill=shadow_color
                )
                
                # Add subtle highlight for depth
                if i == 0:
                    highlight_x = base_x - 1
                    highlight_y = base_y - 1
                    highlight_color = (255, 255, 255, 40)
                    draw.text(
                        (highlight_x, highlight_y),
                        line,
                        font=self.font,
                        fill=highlight_color
                    )
        except Exception as e:
            logging.error(f"3D depth effect error: {e}")

    def _apply_glow_effect(self, draw: ImageDraw.Draw, line: str, base_x: float, base_y: float, intensity: float) -> None:
        """Apply glow effect with improved blending and performance"""
        try:
            glow_intensity = (intensity / 100.0)
            glow_color = ImageColor.getrgb(self.config.settings.font_color)
            glow_radius = int(10 * glow_intensity)
            
            # Cache base text dimensions
            bbox = self.font.getbbox(line)
            text_width = bbox[2] - bbox[0]
            text_height = bbox[3] - bbox[1]
            
            # Create optimized glow pattern
            angles = 12
            for i in range(glow_radius):
                # Calculate alpha with smooth falloff
                alpha = int(100 * (1 - (i/glow_radius)**2) * glow_intensity)
                
                # Optimize angle calculations
                angle_step = math.pi * 2 / angles
                radius = (glow_radius - i) * 1.5
                
                # Pre-calculate sin/cos values
                for angle_idx in range(angles):
                    angle = angle_idx * angle_step
                    dx = math.cos(angle) * radius
                    dy = math.sin(angle) * radius
                    
                    # Apply glow with color modulation
                    glow_x = base_x + dx
                    glow_y = base_y + dy
                    
                    # Add subtle color variation for more natural glow
                    color_mod = 1.0 + (math.sin(angle) * 0.1)
                    modified_color = tuple(
                        min(255, int(c * color_mod))
                        for c in glow_color
                    )
                    
                    draw.text(
                        (glow_x, glow_y),
                        line,
                        font=self.font,
                        fill=(*modified_color, alpha)
                    )
        except Exception as e:
            logging.error(f"Glow effect error: {e}")

    def _apply_rainbow_effect(self, draw: ImageDraw.Draw, line: str, pos_x: float, pos_y: float, alpha: int) -> None:
        """Apply rainbow effect with improved color transitions and performance"""
        try:
            chars = list(line)
            if not chars:
                return
                
            # Calculate base hue progression
            hue_base = (self.current_state.frame_num * 2) % 360
            char_count = len(chars)
            
            # Pre-calculate character widths for positioning
            char_widths = []
            total_width = 0
            for char in chars:
                bbox = self.font.getbbox(char)
                width = bbox[2] - bbox[0]
                char_widths.append(width)
                total_width += width
            
            # Draw characters with optimized color calculation
            current_x = pos_x
            for i, (char, width) in enumerate(zip(chars, char_widths)):
                # Calculate smooth hue progression
                progress = i / char_count
                hue = (hue_base + (progress * 360)) % 360
                
                # Add subtle saturation variation for more vibrant effect
                saturation = 0.9 + math.sin(progress * math.pi) * 0.1
                
                # Calculate RGB with improved color blending
                rgb = self._hsv_to_rgb(hue, saturation, 1.0)
                
                # Draw character with proper alpha
                draw.text(
                    (current_x, pos_y),
                    char,
                    font=self.font,
                    fill=(*rgb, alpha)
                )
                
                current_x += width
        except Exception as e:
            logging.error(f"Rainbow effect error: {e}")

    def _apply_neon_effect(self, draw: ImageDraw.Draw, line: str, pos_x: float, pos_y: float, intensity: float) -> None:
        """Apply neon effect with improved glow and color interaction"""
        try:
            neon_colors = [
                (255, 0, 0),    # Red
                (0, 255, 255),  # Cyan
                (255, 0, 255)   # Magenta
            ]
            neon_intensity = intensity / 100.0
            
            # Pre-calculate base text properties
            bbox = self.font.getbbox(line)
            text_width = bbox[2] - bbox[0]
            
            # Create base glow
            glow_radius = int(4 * neon_intensity)
            base_alpha = int(150 * neon_intensity)
            
            for i, color in enumerate(neon_colors):
                # Calculate dynamic offset based on frame
                phase = self.current_state.frame_num * 0.2 + i * 2.094
                offset = math.sin(phase) * neon_intensity * 4
                
                # Apply color-specific modifications
                for glow_step in range(glow_radius):
                    # Calculate fade-out alpha
                    step_alpha = int(base_alpha * (1 - glow_step/glow_radius))
                    glow_offset = glow_step * 0.5
                    
                    # Draw multiple glow layers
                    for angle in range(8):
                        angle_rad = angle * math.pi / 4
                        dx = math.cos(angle_rad) * glow_offset
                        dy = math.sin(angle_rad) * glow_offset
                        
                        draw.text(
                            (pos_x + offset + dx, pos_y + dy),
                            line,
                            font=self.font,
                            fill=(*color, step_alpha)
                        )
            
            # Draw main text on top
            draw.text(
                (pos_x, pos_y),
                line,
                font=self.font,
                fill=(255, 255, 255, int(255 * neon_intensity))
            )
        except Exception as e:
            logging.error(f"Neon effect error: {e}")

    def _apply_metallic_effect(self, draw: ImageDraw.Draw, line: str, pos_x: float, pos_y: float, intensity: float) -> None:
        """Apply metallic effect with improved reflection and shading"""
        try:
            metallic_intensity = intensity / 100.0
            base_hue = (self.current_state.frame_num * 0.5) % 360
            
            # Pre-calculate text dimensions
            bbox = self.font.getbbox(line)
            text_height = bbox[3] - bbox[1]
            
            # Create metallic gradient layers
            layers = 5
            for i in range(layers):
                # Calculate layer-specific properties
                layer_progress = i / (layers - 1)
                
                # Modulate hue and saturation for metallic appearance
                hue = (base_hue + layer_progress * 30) % 360
                saturation = 0.5 + layer_progress * 0.3
                value = 0.7 + math.sin(layer_progress * math.pi) * 0.3
                
                # Calculate offset with perspective
                offset_x = i * metallic_intensity * 2 * math.cos(layer_progress * math.pi)
                offset_y = i * metallic_intensity * 1.5 * math.sin(layer_progress * math.pi)
                
                # Calculate alpha with smooth falloff
                alpha = int(200 * metallic_intensity * (1 - layer_progress * 0.5))
                
                # Generate metallic color
                color = self._hsv_to_rgb(hue, saturation, value)
                
                # Draw layer with proper blending
                draw.text(
                    (pos_x + offset_x, pos_y + offset_y),
                    line,
                    font=self.font,
                    fill=(*color, alpha)
                )
            
            # Add highlight sparkle effect
            sparkle_count = int(10 * metallic_intensity)
            for _ in range(sparkle_count):
                # Random position within text bounds
                spark_x = pos_x + self.random.uniform(0, bbox[2] - bbox[0])
                spark_y = pos_y + self.random.uniform(0, text_height)
                
                # Draw sparkle
                spark_size = int(2 * metallic_intensity)
                spark_alpha = int(200 * metallic_intensity)
                draw.ellipse(
                    [
                        spark_x - spark_size,
                        spark_y - spark_size,
                        spark_x + spark_size,
                        spark_y + spark_size
                    ],
                    fill=(255, 255, 255, spark_alpha)
                )
        except Exception as e:
            logging.error(f"Metallic effect error: {e}")

    def _apply_wave_effect(self, draw: ImageDraw.Draw, line: str, base_x: float, base_y: float, intensity: float) -> None:
        """Apply wave effect with improved animation and character spacing"""
        try:
            chars = list(line)
            if not chars:
                return
                
            wave_intensity = (intensity / 100.0) * 20
            
            # Pre-calculate character widths
            char_widths = []
            total_width = 0
            for char in chars:
                bbox = self.font.getbbox(char)
                width = bbox[2] - bbox[0]
                char_widths.append(width)
                total_width += width
            
            # Draw characters with wave effect
            current_x = base_x
            for i, (char, width) in enumerate(zip(chars, char_widths)):
                # Calculate wave parameters
                char_progress = i / len(chars)
                phase = self.current_state.frame_num * 0.2 + char_progress * 4
                
                # Combine multiple wave frequencies for more interesting motion
                primary_wave = math.sin(phase) * wave_intensity
                secondary_wave = math.sin(phase * 0.5) * wave_intensity * 0.3
                wave_offset = primary_wave + secondary_wave
                
                # Add subtle horizontal displacement
                x_offset = math.sin(phase * 0.25) * wave_intensity * 0.2
                
                # Draw character with proper position and color
                font_color = ImageColor.getrgb(self.config.settings.font_color)
                draw.text(
                    (current_x + x_offset, base_y + wave_offset),
                    char,
                    font=self.font,
                    fill=(*font_color, 255)
                )
                
                current_x += width
        except Exception as e:
            logging.error(f"Wave effect error: {e}")

    def _apply_outline(self, draw: ImageDraw.Draw, line: str, pos_x: float, pos_y: float, width: int, color: Tuple[int, int, int]) -> None:
        """Apply text outline with improved quality and performance"""
        try:
            # Validate and adjust outline width
            outline_width = max(1, min(width, 5))  # Limit to reasonable range
            
            # Generate outline positions with proper spacing
            positions = []
            for w in range(outline_width):
                w1 = w + 1
                positions.extend([
                    (-w1, -w1), (-w1, 0), (-w1, w1),
                    (0, -w1),            (0, w1),
                    (w1, -w1),  (w1, 0),  (w1, w1)
                ])
            
            # Remove duplicates while maintaining order
            positions = list(dict.fromkeys(map(tuple, positions)))
            
            # Draw outline layers from outside in
            for dx, dy in positions:
                outline_alpha = int(255 * (1 - (math.sqrt(dx*dx + dy*dy) / (outline_width * 1.5))))
                draw.text(
                    (pos_x + dx, pos_y + dy),
                    line,
                    font=self.font,
                    fill=(*color, outline_alpha)
                )
        except Exception as e:
            logging.error(f"Outline effect error: {e}")

    def _apply_typewriter_effect(self, layer: Image.Image, lines: List[str], base_y: float, line_spacing: float) -> None:
        """Apply typewriter effect with improved timing and visuals"""
        try:
            progress = min(1.0, self.current_state.frame_num / (self.current_state.total_frames * 0.5))
            total_chars = sum(len(line) for line in lines)
            chars_to_show = int(total_chars * self._ease_in_out(progress))
            
            # Create mask for progressive reveal
            mask = Image.new('L', layer.size, 0)
            mask_draw = ImageDraw.Draw(mask)
            
            chars_shown = 0
            for line_idx, line in enumerate(lines):
                if chars_shown >= chars_to_show:
                    break
                
                current_y = base_y + (line_idx * line_spacing)
                line_bbox = self.font.getbbox(line)
                line_width = line_bbox[2] - line_bbox[0]
                line_x = (layer.width - line_width) // 2
                
                remaining = chars_to_show - chars_shown
                visible_text = line[:remaining]
                chars_shown += len(visible_text)
                
                if visible_text:
                    # Add cursor effect
                    if chars_shown == chars_to_show and (self.current_state.frame_num % 30) < 15:
                        visible_text += '|'
                    
                    # Draw text with slight motion blur effect
                    for offset in range(2):
                        alpha = 255 if offset == 0 else 128
                        mask_draw.text(
                            (line_x - offset, current_y),
                            visible_text,
                            font=self.font,
                            fill=alpha
                        )
            
            # Apply mask with smooth edges
            layer.putalpha(ImageEnhance.Brightness(mask).enhance(1.2))
            
        except Exception as e:
            logging.error(f"Typewriter effect error: {e}")

    def get_performance_stats(self) -> Dict[str, float]:
        """Return performance statistics for monitoring"""
        try:
            if not self._render_times:
                return {'avg_render_time': 0.0, 'max_render_time': 0.0}
                
            return {
                'avg_render_time': sum(self._render_times) / len(self._render_times),
                'max_render_time': max(self._render_times),
                'cache_size': len(self._canvas_cache),
                'effect_cache_size': len(self._effect_cache)
            }
        except Exception as e:
            logging.error(f"Error getting performance stats: {e}")
            return {'error': 'Failed to calculate performance stats'}

    def optimize_caches(self) -> None:
        """Optimize cache sizes based on memory usage and performance"""
        try:
            # Clear caches if memory usage is too high
            if len(self._canvas_cache) > self._max_cache_size * 0.9:
                logging.info("Optimizing canvas cache size")
                # Keep only the most recently used entries
                keep_count = int(self._max_cache_size * 0.7)
                oldest_keys = sorted(self._canvas_cache.keys())[:-keep_count]
                for key in oldest_keys:
                    del self._canvas_cache[key]

            if len(self._effect_cache) > self._max_cache_size * 0.9:
                logging.info("Optimizing effect cache size")
                keep_count = int(self._max_cache_size * 0.7)
                oldest_keys = sorted(self._effect_cache.keys())[:-keep_count]
                for key in oldest_keys:
                    del self._effect_cache[key]

        except Exception as e:
            logging.error(f"Cache optimization error: {e}")

    def cleanup(self) -> None:
        """Clean up resources with improved memory management"""
        try:
            # Clean up temporary resources
            for resource in self._temp_resources:
                try:
                    if hasattr(resource, 'close'):
                        resource.close()
                except Exception as e:
                    logging.warning(f"Failed to clean up resource: {e}")
            self._temp_resources.clear()

            # Clear caches
            for cache in [self._canvas_cache, self._effect_cache]:
                try:
                    for key in list(cache.keys()):
                        if hasattr(cache[key], 'close'):
                            cache[key].close()
                        del cache[key]
                except Exception as e:
                    logging.warning(f"Failed to clear cache: {e}")
            self._canvas_cache.clear()
            self._effect_cache.clear()

            # Clear any other resources
            self.current_state = None
            self.frame_size = None
            self._render_times.clear()

            # Force garbage collection
            import gc
            gc.collect()

        except Exception as e:
            logging.error(f"Cleanup error: {e}")

    def __del__(self):
        """Ensure proper cleanup on deletion"""
        self.cleanup()

@dataclass
class AppSettings:
    output_directory: str = ""
    resolution: str = "480p"
    fps: int = 10
    font_name: str = "Arial"
    font_size: int = 24
    font_color: str = "#FFFFFF"
    outline_color: str = "#000000"
    outline_width: int = 2
    whisper_model: str = "base"
    max_gif_size_mb: int = 50
    quality: int = 85
    optimize: bool = True
    loop_gif: bool = True
    recent_urls: List[str] = None
    theme: str = "system"
    auto_open_folder: bool = True
    save_format: str = "gif"
    max_recent_urls: int = 10
    resolutions: List[str] = None
    font_sizes: List[int] = None
    available_fonts: List[str] = None
    text_effects: TextEffectSettings = None
    optimization: OptimizationSettings = field(default_factory=OptimizationSettings)

    def __post_init__(self):
        if self.recent_urls is None:
            self.recent_urls = []
        if self.resolutions is None:
            self.resolutions = ["240p", "360p", "480p", "720p", "1080p"]
            self.resolution = "480p"
        if self.font_sizes is None:
            self.font_sizes = [12, 14, 16, 18, 20, 24, 28, 32, 36, 40, 48]
        if self.available_fonts is None:
            self.available_fonts = self._get_system_fonts()
            logging.debug(f"Available fonts: {self.available_fonts}")
        if self.text_effects is None:
            self.text_effects = TextEffectSettings()

    def _get_system_fonts(self) -> List[str]:
        """Get list of available system fonts"""
        if platform.system() == "Windows":
            # Explicitly specify the full paths to common Windows fonts
            fonts_dir = Path("C:/Windows/Fonts")
            font_files = {
                "Arial": "arial.ttf",
                "Impact": "impact.ttf",
                "Bahnschrift": "bahnschrift.ttf",
                "Georgia": "georgia.ttf",
                "Calibri": "calibri.ttf",
                "Tahoma": "tahoma.ttf",
                "Verdana": "verdana.ttf",
                "Segoe UI": "segoeui.ttf",
                "Times New Roman": "times.ttf",
                "Trebuchet MS": "trebuc.ttf"
            }
            
            available_fonts = []
            for font_name, font_file in font_files.items():
                if (fonts_dir / font_file).exists():
                    available_fonts.append(font_name)
                    
            return available_fonts if available_fonts else ["Arial"]
            
        elif platform.system() == "Darwin":  # macOS
            return ["Arial", "Helvetica", "Times New Roman"]
        else:  # Linux
            return ["Liberation Sans", "DejaVu Sans", "FreeSans"]

class ConfigManager:
    def __init__(self, app_dir: Path):
        self.app_dir = app_dir
        self.config_path = app_dir / "config.json"
        self.settings = self._load_settings()
    
    def _load_settings(self) -> AppSettings:
        """Load settings from config file"""
        if self.config_path.exists():
            try:
                with open(self.config_path, 'r') as f:
                    data = json.load(f)
                
                # Convert text_effects dict back to TextEffectSettings
                if 'text_effects' in data:
                    effects_data = data['text_effects']
                    text_effects = TextEffectSettings()
                    for effect_name, effect_data in effects_data.items():
                        if hasattr(text_effects, effect_name):
                            effect = getattr(text_effects, effect_name)
                            effect.enabled = effect_data.get('enabled', False)
                            effect.intensity = effect_data.get('intensity', 50)
                    data['text_effects'] = text_effects

                # Convert optimization settings
                if 'optimization' in data:
                    opt_data = data['optimization']
                    
                    # Convert frame timings
                    if 'frame_timings' in opt_data:
                        opt_data['frame_timings'] = [
                            FrameTiming(**timing) for timing in opt_data['frame_timings']
                        ]
                    
                    # Convert motion regions
                    if 'motion_regions' in opt_data:
                        opt_data['motion_regions'] = [
                            MotionRegion(**region) for region in opt_data['motion_regions']
                        ]
                    
                    data['optimization'] = OptimizationSettings(**opt_data)
                    
                return AppSettings(**data)
            except Exception as e:
                logging.error(f"Error loading config: {e}")
        return AppSettings()
    
    def save_settings(self):
        """Save settings to config file with better text effects handling"""
        try:
            # Convert settings to dict
            settings_dict = asdict(self.settings)
            
            # Special handling for text effects
            if 'text_effects' in settings_dict:
                effects_dict = {}
                for effect_name, effect in vars(self.settings.text_effects).items():
                    if isinstance(effect, TextEffect):
                        effects_dict[effect_name] = {
                            'enabled': effect.enabled,
                            'intensity': effect.intensity,
                            'name': effect.name
                        }
                settings_dict['text_effects'] = effects_dict
            
            # Save with pretty printing
            with open(self.config_path, 'w') as f:
                json.dump(settings_dict, f, indent=4)
                
            # Log successful save
            logging.info("Settings saved successfully")
            logging.debug(f"Saved settings: {settings_dict}")
            
        except Exception as e:
            logging.error(f"Error saving config: {e}")
            raise
    
    def update_settings(self, **kwargs):
        """Update settings with new values"""
        for key, value in kwargs.items():
            if hasattr(self.settings, key):
                setattr(self.settings, key, value)
        self.save_settings()

class CaptionEditor(tk.Toplevel):
    def __init__(self, parent, segments: List[VideoSegment], video_path: str, config: 'ConfigManager', gif_renderer: 'GIFRenderer'):
        super().__init__(parent)
        self.parent = parent
        self.config = config
        self.gif_renderer = gif_renderer
        self.segments = segments
        self.edited_segments = None
        self.video_path = video_path
        self.cap = None
        self.current_frame = None
        self.current_frame_idx = 0
        self.total_frames = 0
        self.fps = 0
        self.playing = False
        self.play_thread = None
        self._updating_timeline = False
        self.start_time = 0.0
        self.end_time = 0.0
        self.start_marker = None
        self.end_marker = None
        self.timeline_canvas = None
        self.current_photo = None
        self.preview_canvas = None
        self.time_label = None
        self.font = None
        
        self.title("Edit Captions")

        # Make window modal and set focus
        self.transient(parent)
        self.grab_set()

        # Configure window
        self.minsize(800, 700)  # Increased minimum height

        # Set up dynamic sizing
        self.columnconfigure(0, weight=1)
        self.rowconfigure(0, weight=1)

        # Calculate initial size based on screen dimensions
        screen_width = self.winfo_screenwidth()
        screen_height = self.winfo_screenheight()
        width = min(1024, int(screen_width * 0.8))
        height = min(868, int(screen_height * 0.8))  # Increased height

        # Create UI before initializing video
        self.create_ui()

        # Initialize video capture
        self.setup_video()

        # Set size and position
        self.geometry(f"{width}x{height}")

        # Center window
        x = (screen_width // 2) - (width // 2)
        y = (screen_height // 2) - (height // 2)
        self.geometry(f"+{x}+{y}")

        # Load font
        self._load_font()

        # Ensure window is on top and focused
        self.lift()
        self.focus_force()

        # Bind window resize event
        self.bind("<Configure>", self.on_resize)

        # Start preview update
        self.after(100, self.update_preview)

        # Bind closing event
        self.protocol("WM_DELETE_WINDOW", self.on_closing)

    def _load_font(self):
        """Load font with error handling and fallbacks"""
        try:
            # Changed from parent.config to self.config since we now pass it directly
            font_name = self.config.settings.font_name
            font_size = self.config.settings.font_size
            
            # Try loading from Windows Fonts directory first
            if platform.system() == "Windows":
                # Handle common font name variations
                font_files = {
                    'Arial': 'arial.ttf',
                    'Times New Roman': 'times.ttf',
                    'Impact': 'impact.ttf',
                }
                font_file = font_files.get(font_name, f"{font_name.lower()}.ttf")
                font_path = Path("C:/Windows/Fonts") / font_file
                
                if font_path.exists():
                    self.font = ImageFont.truetype(str(font_path), font_size)
                    logging.debug(f"Loaded font: {font_path}")
                    return
                    
            # Try Arial as primary fallback
            try:
                arial_path = Path("C:/Windows/Fonts/arial.ttf")
                if arial_path.exists():
                    self.font = ImageFont.truetype(str(arial_path), font_size)
                    logging.debug("Using Arial fallback")
                    return
            except Exception as e:
                logging.warning(f"Could not load Arial font: {e}")
                
            # Last resort: default font
            self.font = ImageFont.load_default()
            logging.warning("Using default font as fallback")
            
        except Exception as e:
            logging.error(f"Font loading error: {e}")
            logging.debug(f"Config: {self.config}")  # Add debug logging
            self.font = ImageFont.load_default()

    def create_ui(self):
        """Create the caption editor UI with improved preview pane and timeline"""
        # Main frame with padding and dynamic sizing
        main_frame = ttk.Frame(self, padding="10")
        main_frame.grid(row=0, column=0, sticky="nsew")
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(1, weight=2)  # Give more weight to the text area

        # Preview frame at the top
        preview_frame = ttk.LabelFrame(main_frame, text="Video Preview", padding="5")
        preview_frame.grid(row=0, column=0, sticky="nsew", pady=(0, 10))
        preview_frame.columnconfigure(0, weight=1)
        preview_frame.rowconfigure(0, weight=1)

        # Preview canvas with larger size
        self.preview_canvas = tk.Canvas(
            preview_frame,
            width=640,
            height=360,
            bg="black"
        )
        self.preview_canvas.grid(row=0, column=0, sticky="nsew", padx=5, pady=5)

        # Timeline control frame
        timeline_frame = ttk.Frame(preview_frame)
        timeline_frame.grid(row=1, column=0, sticky="ew", padx=5, pady=5)
        timeline_frame.columnconfigure(1, weight=1)

        # Play/Pause button
        self.play_button = ttk.Button(
            timeline_frame,
            text="▶",
            width=3,
            command=self.toggle_play
        )
        self.play_button.grid(row=0, column=0, padx=(0, 5))

        # Timeline canvas for custom markers
        self.timeline_canvas = tk.Canvas(
            timeline_frame,
            height=30,
            bg="white",
            highlightthickness=1,
            highlightbackground="gray"
        )
        self.timeline_canvas.grid(row=0, column=1, sticky="ew", padx=5)

        # Bind timeline canvas events
        self.timeline_canvas.bind("<Button-1>", self.on_timeline_click)
        self.timeline_canvas.bind("<B1-Motion>", self.on_timeline_drag)

        # Time display
        self.time_label = ttk.Label(timeline_frame, text="0:00 / 0:00")
        self.time_label.grid(row=0, column=2, padx=(5, 0))

        # Create text widget frame with more vertical space
        text_frame = ttk.LabelFrame(main_frame, text="Captions", padding="5")
        text_frame.grid(row=1, column=0, sticky="nsew")
        text_frame.columnconfigure(0, weight=1)
        text_frame.rowconfigure(0, weight=1)

        # Text widget with scrollbar and larger default size
        self.text_widget = scrolledtext.ScrolledText(
            text_frame,
            wrap=tk.WORD,
            undo=True,
            height=15,  # Increased height for better visibility
            font=("TkDefaultFont", 11)  # Slightly larger font
        )
        self.text_widget.grid(row=0, column=0, sticky="nsew")

        # Load segments into text widget
        for segment in self.segments:
            time_str = f"{segment.start_time:.2f} - {segment.end_time:.2f}: "
            self.text_widget.insert(tk.END, time_str)
            self.text_widget.insert(tk.END, f"{segment.text}\n\n")

        # Button frame
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=2, column=0, sticky="ew", pady=10)
        button_frame.columnconfigure(1, weight=1)

        # Save button
        save_button = ttk.Button(
            button_frame,
            text="Save",
            command=self.save_captions,
            width=15
        )
        save_button.grid(row=0, column=0, padx=5)

        # Cancel button
        cancel_button = ttk.Button(
            button_frame,
            text="Cancel",
            command=self.destroy,
            width=15
        )
        cancel_button.grid(row=0, column=1, sticky="e", padx=5)

    def on_timeline_click(self, event):
        """Handle clicks on timeline canvas"""
        try:
            canvas_width = self.timeline_canvas.winfo_width()
            if canvas_width <= 1:  # Canvas not properly initialized
                return
                
            # Calculate precise frame position
            click_pos = event.x / canvas_width
            frame_num = int(click_pos * self.total_frames)
            exact_time = frame_num / self.fps
            
            # Determine if click is closer to start or end marker
            if self.start_time is None or abs(exact_time - self.start_time) <= abs(exact_time - self.end_time):
                self.start_time = exact_time
                self.update_timeline_markers()
            else:
                self.end_time = exact_time
                self.update_timeline_markers()
            
            # Seek to exact frame
            self.seek_frame(frame_num)
            
        except Exception as e:
            logging.error(f"Timeline click error: {e}")

    def on_timeline_drag(self, event):
        """Handle dragging markers on timeline"""
        try:
            canvas_width = self.timeline_canvas.winfo_width()
            if canvas_width <= 1:
                return
                
            # Calculate new time position
            pos = max(0, min(event.x, canvas_width)) / canvas_width
            new_time = pos * (self.total_frames / self.fps)
            
            # Update the appropriate marker
            if self.start_marker and abs(event.x - self.timeline_canvas.coords(self.start_marker)[0]) < 10:
                self.start_time = new_time
            elif self.end_marker and abs(event.x - self.timeline_canvas.coords(self.end_marker)[0]) < 10:
                self.end_time = new_time
            
            self.update_timeline_markers()
            self.seek_frame(int(pos * self.total_frames))
            
        except Exception as e:
            logging.error(f"Timeline drag error: {e}")

    def update_timeline_markers(self):
        """Update timeline markers and progress indicator"""
        try:
            canvas_width = self.timeline_canvas.winfo_width()
            canvas_height = self.timeline_canvas.winfo_height()
            
            # Clear existing markers
            self.timeline_canvas.delete("all")
            
            # Draw timeline base
            self.timeline_canvas.create_rectangle(
                0, 0, canvas_width, canvas_height,
                fill="white", outline="gray"
            )
            
            # Draw progress bar
            if self.total_frames > 0:
                progress = (self.current_frame_idx / self.total_frames) * canvas_width
                self.timeline_canvas.create_rectangle(
                    0, 0, progress, canvas_height,
                    fill="#e0e0e0", outline=""
                )
            
            # Draw start marker (green)
            if self.start_time is not None:
                start_x = (self.start_time * self.fps / self.total_frames) * canvas_width
                self.start_marker = self.timeline_canvas.create_polygon(
                    start_x, 0,
                    start_x + 10, canvas_height//2,
                    start_x, canvas_height,
                    fill="#4CAF50", outline="#388E3C"
                )
            
            # Draw end marker (red)
            if self.end_time is not None:
                end_x = (self.end_time * self.fps / self.total_frames) * canvas_width
                self.end_marker = self.timeline_canvas.create_polygon(
                    end_x, 0,
                    end_x - 10, canvas_height//2,
                    end_x, canvas_height,
                    fill="#F44336", outline="#D32F2F"
                )
            
        except Exception as e:
            logging.error(f"Timeline marker update error: {e}")

    def setup_video(self):
        """Initialize video capture and get video properties"""
        try:
            self.cap = cv2.VideoCapture(self.video_path)
            if not self.cap.isOpened():
                raise Exception("Failed to open video file")
            
            self.total_frames = int(self.cap.get(cv2.CAP_PROP_FRAME_COUNT))
            self.fps = self.cap.get(cv2.CAP_PROP_FPS)
            
            # Set initial frame
            self.seek_frame(0)
            
            # Initialize end time
            self.end_time = self.total_frames / self.fps
            
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load video: {str(e)}")
            self.destroy()

    def seek_frame(self, frame_idx: int):
        """Seek to specific frame in video"""
        try:
            frame_idx = max(0, min(frame_idx, self.total_frames - 1))
            self.cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)
            ret, frame = self.cap.read()
            if ret:
                self.current_frame_idx = frame_idx
                self.current_frame = frame
                self.update_preview_image()
                self.update_timeline_markers()
                self.update_time_display()
        except Exception as e:
            logging.error(f"Error seeking frame: {e}")

    def update_preview_image(self):
        """Update preview canvas with current frame and captions using GIFRenderer"""
        try:
            if self.current_frame is None:
                return

            # Convert BGR to RGB
            frame_rgb = cv2.cvtColor(self.current_frame, cv2.COLOR_BGR2RGB)

            # Get canvas size
            canvas_width = self.preview_canvas.winfo_width()
            canvas_height = self.preview_canvas.winfo_height()

            if canvas_width <= 1 or canvas_height <= 1:
                return

            # Calculate aspect ratio
            frame_height, frame_width = frame_rgb.shape[:2]
            frame_aspect = frame_width / frame_height
            canvas_aspect = canvas_width / canvas_height

            # Calculate dimensions to maintain aspect ratio
            if frame_aspect > canvas_aspect:
                # Width limited by canvas
                new_width = canvas_width
                new_height = int(canvas_width / frame_aspect)
            else:
                # Height limited by canvas
                new_height = canvas_height
                new_width = int(canvas_height * frame_aspect)

            # Resize frame
            frame_resized = cv2.resize(frame_rgb, (new_width, new_height))

            # Convert to PIL Image
            image = Image.fromarray(frame_resized)

            # Get current caption
            current_time = self.current_frame_idx / self.fps
            current_segment = None
            for segment in self.segments:
                if segment.start_time <= current_time <= segment.end_time:
                    current_segment = segment
                    break

            # Process frame with GIFRenderer for text overlay with effects
            processed_image = image.copy()
            if current_segment:
                processed_image = self.gif_renderer._process_frame(
                    processed_image,
                    self.current_frame_idx,
                    self.total_frames,
                    current_segment,
                    None  # No previous frame needed for preview
                )

            # Create centered frame
            final_image = Image.new('RGBA', (canvas_width, canvas_height), (0, 0, 0, 0))
            paste_x = (canvas_width - new_width) // 2
            paste_y = (canvas_height - new_height) // 2
            final_image.paste(processed_image, (paste_x, paste_y))

            # Convert to PhotoImage
            photo = ImageTk.PhotoImage(final_image)
            self.current_photo = photo  # Keep reference to prevent garbage collection

            # Update canvas
            self.preview_canvas.delete("all")
            self.preview_canvas.create_image(0, 0, anchor="nw", image=photo)

            # Clean up
            image.close()
            if processed_image is not image:
                processed_image.close()

        except Exception as e:
            logging.error(f"Error updating preview: {e}")
            logging.error(traceback.format_exc())  # Full stack trace for debugging

    def update_preview(self):
        """Regular preview update check"""
        try:
            if self.current_frame is not None:
                self.update_preview_image()
                self.update_timeline_markers()

            # Schedule next update if window still exists
            if self.winfo_exists():
                self.after(100, self.update_preview)

        except Exception as e:
            logging.error(f"Error in preview update: {e}")

    def _wrap_text(self, text: str, max_width: float) -> List[str]:
        """Wrap text to fit within max_width pixels"""
        words = text.strip().split()
        lines = []
        current_line = ''
        
        for word in words:
            # Test line with new word
            test_line = f"{current_line} {word}".strip()
            bbox = self.font.getbbox(test_line)
            
            if bbox[2] <= max_width:  # bbox[2] is right edge of text
                current_line = test_line
            else:
                if current_line:
                    lines.append(current_line)
                current_line = word
                
        if current_line:
            lines.append(current_line)
            
        return lines

    def get_current_caption(self, current_time: float) -> Optional[str]:
        """Get caption text for the current time"""
        for segment in self.segments:
            if segment.start_time <= current_time <= segment.end_time:
                return segment.text
        return None

    def update_time_display(self):
        """Update time display label with frame-accurate timing"""
        try:
            current_frame = self.current_frame_idx
            current_time = current_frame / self.fps
            total_time = self.total_frames / self.fps

            # Show frame numbers along with time
            current_str = f"{self.format_time(current_time)} (f{current_frame})"
            total_str = f"{self.format_time(total_time)} (f{self.total_frames})"

            self.time_label.configure(text=f"{current_str} / {total_str}")

        except Exception as e:
            logging.error(f"Error updating time display: {e}")

    def toggle_play(self):
        """Toggle video playback"""
        if self.playing:
            self.playing = False
            self.play_button.configure(text="▶")
        else:
            self.playing = True
            self.play_button.configure(text="⏸")
            threading.Thread(target=self.play_video, daemon=True).start()

    def play_video(self):
        """Play video in a separate thread"""
        try:
            while self.playing and self.current_frame_idx < self.total_frames - 1:
                frame_time = 1 / self.fps
                start_time = time.time()

                # Get next frame
                ret, frame = self.cap.read()
                if not ret:
                    break

                # Store frame and update UI
                self.current_frame = frame
                self.current_frame_idx += 1

                # Update UI in main thread
                self.after(0, self.update_preview_image)
                self.after(0, self.update_timeline_markers)
                self.after(0, self.update_time_display)

                # Maintain correct playback speed
                elapsed = time.time() - start_time
                sleep_time = max(0, frame_time - elapsed)
                time.sleep(sleep_time)

            # Reset play state
            self.playing = False
            self.after(0, lambda: self.play_button.configure(text="▶"))

        except Exception as e:
            logging.error(f"Error during video playback: {e}")
            self.playing = False
            self.after(0, lambda: self.play_button.configure(text="▶"))

    def format_time(self, seconds: float) -> str:
        """Format time in seconds to MM:SS.mmm"""
        minutes = int(seconds // 60)
        seconds_part = seconds % 60
        return f"{minutes}:{seconds_part:06.3f}"

    def on_resize(self, event):
        """Handle window resize events"""
        if event.widget == self:
            # Minimum sizes
            if event.width < 800:
                self.geometry(f"800x{event.height}")
            if event.height < 700:
                self.geometry(f"{event.width}x700")

            # Update preview if we have a frame
            if self.current_frame is not None:
                self.update_preview_image()
                self.update_timeline_markers()

    def on_closing(self):
        """Clean up resources when closing"""
        try:
            self.playing = False
            if hasattr(self, 'play_thread') and self.play_thread and self.play_thread.is_alive():
                self.play_thread.join()

            if self.cap:
                self.cap.release()

            self.destroy()

        except Exception as e:
            logging.error(f"Error during cleanup: {e}")
            self.destroy()

    def save_captions(self):
        """Parse and save edited captions with time range"""
        try:
            if self.start_time is None or self.end_time is None:
                raise ValueError("Please set both start and end times")

            # Calculate exact frame positions
            start_frame = int(self.start_time * self.fps)
            end_frame = int(self.end_time * self.fps)
            
            # Get precise times from frame positions
            exact_start = start_frame / self.fps
            exact_end = end_frame / self.fps
            
            logging.debug(f"Saving with start time: {exact_start:.3f}s (frame {start_frame})")
            logging.debug(f"Saving with end time: {exact_end:.3f}s (frame {end_frame})")

            text = self.text_widget.get("1.0", tk.END)
            lines = text.strip().split('\n')
            new_segments = []

            for line in lines:
                line = line.strip()
                if not line:
                    continue

                # Parse line with improved precision
                match = re.match(r'(\d+\.?\d*)\s*-\s*(\d+\.?\d*)\s*:\s*(.+)', line)
                if not match:
                    continue

                seg_start = float(match.group(1))
                seg_end = float(match.group(2))
                text = match.group(3).strip()

                # Adjust segment times to be within selected range
                if seg_end < exact_start or seg_start > exact_end:
                    continue

                seg_start = max(seg_start, exact_start)
                seg_end = min(seg_end, exact_end)

                # Don't add invalid segments
                if seg_start >= seg_end:
                    continue

                new_segments.append(VideoSegment(
                    start_time=seg_start,
                    end_time=seg_end,
                    text=text
                ))

            # Store the exact cut times along with the segments
            self.edited_segments = new_segments
            self.final_start_time = exact_start
            self.final_end_time = exact_end
            
            self.destroy()

        except Exception as e:
            logging.error(f"Error parsing captions: {str(e)}")
            messagebox.showerror(
                "Error",
                f"Error parsing captions: {str(e)}\n\n"
                "Please use format: start_time - end_time: caption text"
            )

class GIFRenderer:
    def __init__(self, config: 'ConfigManager'):
        self.config = config
        self.app_dir = config.app_dir
        self.prev_frame = None
        self._temp_images = []
        self.font = None
        self._load_font()
        
    def _load_font(self):
        """Load font with error handling and fallbacks"""
        try:
            font_name = self.config.settings.font_name
            font_size = self.config.settings.font_size
            
            # Try loading from Windows Fonts directory first
            if platform.system() == "Windows":
                font_path = Path("C:/Windows/Fonts") / f"{font_name.lower()}.ttf"
                if font_path.exists():
                    self.font = ImageFont.truetype(str(font_path), font_size)
                    return
                    
            # Try loading directly by name
            try:
                self.font = ImageFont.truetype(font_name, font_size)
                return
            except Exception as e:
                logging.warning(f"Could not load system font {font_name}: {e}")
            
            # Try Arial as fallback
            try:
                self.font = ImageFont.truetype("arial.ttf", font_size)
                return
            except:
                pass
                
            # Last resort: default font
            self.font = ImageFont.load_default()
            logging.warning("Using default font as fallback")
            
        except Exception as e:
            logging.error(f"Font loading error: {e}")
            self.font = ImageFont.load_default()

    def cleanup(self):
        """Clean up resources"""
        try:
            # Close and cleanup temporary images
            for img in self._temp_images:
                try:
                    img.close()
                except Exception as e:
                    logging.warning(f"Failed to close image: {e}")
            self._temp_images.clear()
            
            # Clear previous frame
            if self.prev_frame:
                try:
                    self.prev_frame.close()
                except:
                    pass
                self.prev_frame = None
                
        except Exception as e:
            logging.error(f"GIF renderer cleanup error: {e}")

    def optimize_frame_colors(self, frame: Image.Image) -> Image.Image:
        """Apply color optimization settings to frame"""
        try:
            settings = self.config.settings.optimization
        
            # If color_limit is 0, return original frame
            if settings.color_limit == 0:
                return frame
            
            # Convert frame to RGBA first
            frame = frame.convert('RGBA')
        
            # Extract alpha channel
            alpha = frame.split()[3]
        
            # Create RGB image with white background
            rgb_frame = Image.new('RGB', frame.size, (255, 255, 255))
            rgb_frame.paste(frame, mask=alpha)
        
            # Create base palette
            base_palette = []
        
            if settings.web_safe_colors:
                # Add web-safe colors (216 colors)
                for r in range(0, 256, 51):
                    for g in range(0, 256, 51):
                        for b in range(0, 256, 51):
                            base_palette.extend([r, g, b])
            else:
                # Create adaptive palette from image
                quantized = rgb_frame.quantize(colors=min(settings.color_limit or 256, 256))
                base_palette = quantized.getpalette()[:768]  # Get RGB values
        
            # Ensure palette has exactly 256 colors
            while len(base_palette) < 768:  # 256 colors * 3 channels
                base_palette.extend([0, 0, 0])
            base_palette = base_palette[:768]
        
            # Create palette image
            palette_img = Image.new('P', (1, 1))
            palette_img.putpalette(base_palette)
        
            # Convert frame using palette
            try:
                dither_mode = getattr(Image, settings.dither_mode)
            except AttributeError:
                logging.warning(f"Invalid dither mode {settings.dither_mode}, falling back to FLOYDSTEINBERG")
                dither_mode = Image.FLOYDSTEINBERG
            
            frame = rgb_frame.quantize(
                palette=palette_img,
                dither=dither_mode
            )
        
            # Convert back to RGBA and restore alpha
            frame = frame.convert('RGBA')
            frame.putalpha(alpha)
        
            return frame
        
        except Exception as e:
            logging.error(f"Color optimization error: {e}")
            # Return original frame if optimization fails
            return frame

    def apply_motion_regions(self, current_frame: Image.Image, prev_frame: Image.Image) -> Image.Image:
        """Apply motion region processing to frame"""
        try:
            settings = self.config.settings.optimization
            
            # If no motion regions defined or detection disabled, return original frame
            if not settings.motion_regions or not settings.detect_static_frames:
                return current_frame
                
            # Convert frames to numpy arrays for processing
            curr_array = np.array(current_frame)
            prev_array = np.array(prev_frame) if prev_frame else curr_array
            
            # Create mask for motion regions
            mask = np.zeros(curr_array.shape[:2], dtype=np.uint8)
            
            for region in settings.motion_regions:
                if not region.enabled:
                    continue
                    
                # Fill region in mask
                mask[region.y1:region.y2, region.x1:region.x2] = 255
                
                if region.fade_edges:
                    # Apply gaussian blur to edges
                    edge_size = 5
                    mask_region = mask[region.y1:region.y2, region.x1:region.x2]
                    cv2.GaussianBlur(mask_region, (edge_size, edge_size), 0, mask_region)
            
            # Convert mask to 3D for multiplication
            mask_3d = np.stack([mask] * curr_array.shape[2], axis=2) / 255.0
            
            # Blend frames based on motion mask
            result = curr_array * mask_3d + prev_array * (1 - mask_3d)
            
            # Convert back to PIL Image
            return Image.fromarray(result.astype(np.uint8))
            
        except Exception as e:
            logging.error(f"Motion region processing error: {e}")
            return current_frame

class VideoProcessor:
    def __init__(self, config: 'ConfigManager'):
        self.config = config
        self.cancel_flag = False
        self.app = None
        self.whisper_model = None
        self.frame_cache = {}
        self._temp_files = set()  # Track temporary files
        self._temp_dir = config.app_dir / "temp"  # Store reference to temp directory
        self._temp_images = []  # Change to list instead of set
        self._ensure_temp_dir()
        self.gif_renderer = GIFRenderer(config)

    def _ensure_temp_dir(self):
        """Ensure temporary directory exists"""
        try:
            self._temp_dir.mkdir(parents=True, exist_ok=True)
        except Exception as e:
            logging.error(f"Failed to create temp directory: {e}")
            raise

    def set_app(self, app: 'AutoGIFApp'):
        """Set reference to main app instance"""
        self.app = app

    def cleanup(self):
        """Clean up resources"""
        try:
            # Clear frame cache
            self.frame_cache.clear()
            
            # Close and cleanup temporary images
            for img in self._temp_images:
                try:
                    img.close()
                except Exception as e:
                    logging.warning(f"Failed to close image: {e}")
            self._temp_images.clear()
            
            # Clean up GIF renderer
            if self.gif_renderer:
                self.gif_renderer.cleanup()
                
            # Clean up temp files
            for file in self._temp_files:
                try:
                    if os.path.exists(file):
                        os.remove(file)
                except Exception as e:
                    logging.warning(f"Failed to remove temp file {file}: {e}")
            self._temp_files.clear()
            
        except Exception as e:
            logging.error(f"Cleanup error: {e}")

    def _get_resolution_height(self, resolution: str) -> int:
        """Convert resolution string to height in pixels"""
        try:
            return int(resolution.replace('p', ''))
        except:
            return 480  # Default to 480p

    def update_status(self, message: str, progress: float = None):
        """Update status via app reference"""
        if self.app:
            self.app.update_status(message, progress)

    def download_segment(self, url: str, start_time: float, duration: float) -> str:
        """Download video segment from YouTube"""
        try:
            self.update_status("Downloading video...")
            
            # Ensure output directory exists
            os.makedirs(self._temp_dir, exist_ok=True)

            # Configure yt-dlp options
            ydl_opts = {
                'format': f'bestvideo[height<=?{self._get_resolution_height(self.config.settings.resolution)}]+bestaudio/best',
                'outtmpl': str(self._temp_dir / 'video.%(ext)s'),
                'quiet': True,
                'no_warnings': True,
                'logger': logging.getLogger('yt_dlp')
            }

            # Download video
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                try:
                    info_dict = ydl.extract_info(url, download=True)
                    video_ext = info_dict.get('ext', 'mp4')
                except Exception as e:
                    logging.error(f"yt-dlp download error: {e}")
                    raise Exception(f"Failed to download video with yt-dlp: {str(e)}")

            # Update input and output paths based on the actual extension
            input_path = self._temp_dir / f'video.{video_ext}'
            output_path = self._temp_dir / 'video_segment.mp4'

            # Check if the video file was downloaded
            if not input_path.exists():
                raise Exception("Failed to download video with yt-dlp")

            # Track temporary files
            self._temp_files.add(str(input_path))
            self._temp_files.add(str(output_path))

            # Use ffmpeg to extract segment with precise timing
            try:
                ffmpeg_cmd = [
                    'ffmpeg',
                    '-ss', f"{start_time:.3f}",  # Use millisecond precision
                    '-i', str(input_path),
                    '-t', f"{duration:.3f}",     # Use millisecond precision
                    '-c:v', 'libx264',
                    '-c:a', 'aac',
                    '-copyts',                   # Maintain timestamp accuracy
                    '-avoid_negative_ts', '1',
                    '-y',
                    str(output_path)
                ]

                result = subprocess.run(ffmpeg_cmd, capture_output=True, text=True)
                if result.returncode != 0:
                    logging.error(f"FFmpeg stderr: {result.stderr}")
                    raise Exception(f"FFmpeg error: {result.stderr}")

            except Exception as e:
                logging.error(f"FFmpeg processing error: {e}")
                raise Exception(f"Failed to process video segment: {str(e)}")

            finally:
                # Clean up temp input file
                try:
                    if input_path.exists():
                        input_path.unlink()
                        self._temp_files.remove(str(input_path))
                except Exception as e:
                    logging.warning(f"Failed to clean up temp file: {e}")

            return str(output_path)

        except Exception as e:
            logging.error(f"Download error: {e}")
            raise Exception(f"Failed to download video: {str(e)}")

    def extract_audio(self, video_path: str) -> str:
        """Extract audio from video file"""
        try:
            self.update_status("Extracting audio...")
            output_path = self._temp_dir / 'audio.wav'
            self._temp_files.add(str(output_path))
            
            ffmpeg_cmd = [
                'ffmpeg',
                '-i', video_path,
                '-vn',              # Disable video
                '-acodec', 'pcm_s16le',  # Use PCM format
                '-ar', '16000',     # 16kHz sample rate
                '-ac', '1',         # Mono audio
                '-y',               # Overwrite output
                str(output_path)
            ]
            
            result = subprocess.run(ffmpeg_cmd, capture_output=True, text=True)
            if result.returncode != 0:
                raise Exception(f"FFMPEG error: {result.stderr}")
                
            return str(output_path)
            
        except Exception as e:
            logging.error(f"Audio extraction error: {e}")
            raise Exception(f"Failed to extract audio: {str(e)}")

    def generate_subtitles(self, audio_path: str) -> List[VideoSegment]:
        """Generate subtitles using Whisper"""
        try:
            self.update_status("Generating subtitles...")
            
            # Load Whisper model if not already loaded
            if self.whisper_model is None:
                self.whisper_model = whisper.load_model(self.config.settings.whisper_model)
            
            # Transcribe audio
            result = self.whisper_model.transcribe(
                audio_path,
                language="en",
                task="transcribe",
                fp16=False
            )
            
            # Convert segments to VideoSegment objects
            segments = []
            for segment in result["segments"]:
                segments.append(VideoSegment(
                    start_time=segment["start"],
                    end_time=segment["end"],
                    text=segment["text"].strip()
                ))
            
            return segments
            
        except Exception as e:
            logging.error(f"Subtitle generation error: {e}")
            raise Exception(f"Failed to generate subtitles: {str(e)}")

    def create_gif(self, video_path: str, output_path: str, fps: int, segments: List[VideoSegment]):
        """Create GIF from video with subtitles"""
        cap = None
        try:
            cap = cv2.VideoCapture(video_path)
            if not cap.isOpened():
                raise Exception("Failed to open video file")

            # Get video properties
            video_fps = cap.get(cv2.CAP_PROP_FPS)
            
            # Calculate exact start and end frames based on first and last segments
            if segments:
                first_seg = min(segments, key=lambda s: s.start_time)
                last_seg = max(segments, key=lambda s: s.end_time)
                start_frame = int(first_seg.start_time * video_fps)
                end_frame = int(last_seg.end_time * video_fps)
            else:
                start_frame = 0
                end_frame = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))

            # Calculate frame step for desired output FPS
            skip_frames = max(1, int(video_fps / fps))
            
            # Generate list of frames to capture
            frame_indices = range(start_frame, end_frame, skip_frames)
            frames = []
            prev_frame = None

            for frame_idx in frame_indices:
                if self.cancel_flag:
                    raise Exception("Operation cancelled")

                # Seek to exact frame
                cap.set(cv2.CAP_PROP_POS_FRAMES, frame_idx)
                ret, frame = cap.read()
                if not ret:
                    break

                # Calculate exact time for this frame
                current_time = frame_idx / video_fps

                # Process frame
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                pil_image = Image.fromarray(frame_rgb)

                # Find current subtitle
                current_segment = None
                for segment in segments:
                    if segment.start_time <= current_time <= segment.end_time:
                        current_segment = segment
                        break

                # Process frame with text overlay
                pil_image = self._process_frame(
                    pil_image,
                    frame_idx - start_frame,  # Adjust frame index relative to start
                    end_frame - start_frame,
                    current_segment,
                    prev_frame
                )

                frames.append(pil_image)
                prev_frame = pil_image.copy()

                # Update progress
                progress = ((frame_idx - start_frame) / (end_frame - start_frame)) * 100
                self.update_status(f"Creating GIF: {progress:.1f}%", progress)

            if not frames:
                raise Exception("No frames were processed")

            # Save GIF with exact frame duration
            self.update_status("Saving GIF...")
            duration = 1000.0 / fps  # Convert to milliseconds
            imageio.mimsave(
                output_path,
                frames,
                duration=duration,
                loop=0 if self.config.settings.loop_gif else 1,
                quality=self.config.settings.quality
            )

            self.update_status("GIF created successfully!", 100)

        except Exception as e:
            logging.error(f"GIF creation error: {e}")
            raise Exception(f"Failed to create GIF: {str(e)}")

        finally:
            if cap:
                cap.release()
            # Clean up temp images
            for frame in frames:
                try:
                    if hasattr(frame, 'close'):
                        frame.close()
                except:
                    pass

    def _process_frame(self, frame: Image.Image, frame_idx: int, total_frames: int, 
                      current_segment: Optional[VideoSegment], prev_frame: Optional[Image.Image]) -> Image.Image:
        """Process a single frame with text overlay and effects"""
        try:
            # Convert frame to RGBA for transparency support
            frame = frame.convert('RGBA')
            self._temp_images.append(frame)
        
            # Create effect manager if not exists
            if not hasattr(self, 'effect_manager'):
                self.effect_manager = EffectManager(self.config)
        
            # Apply optimization settings through GIF renderer
            frame = self.gif_renderer.optimize_frame_colors(frame)
        
            # Apply motion region processing if previous frame exists
            if prev_frame:
                frame = self.gif_renderer.apply_motion_regions(frame, prev_frame)
        
            # Add text overlay if we have a current segment
            if current_segment:
                # Calculate base text position
                text_bbox = self.effect_manager.font.getbbox(current_segment.text)
                text_width = text_bbox[2] - text_bbox[0]
                text_height = text_bbox[3] - text_bbox[1]
                base_x = (frame.width - text_width) // 2
                base_y = frame.height - text_height - 20
            
                # Prepare frame for effects
                self.effect_manager.prepare_frame(frame, frame_idx, total_frames)
            
                # Apply all text effects in a single pass
                frame = self.effect_manager.render_text(
                    frame=frame,
                    text=current_segment.text,
                    base_position=(base_x, base_y)
                )
        
            # Apply any final frame optimizations
            if self.config.settings.optimization.detect_static_frames and prev_frame:
                curr_array = np.array(frame)
                prev_array = np.array(prev_frame)
                diff = np.mean(np.abs(curr_array - prev_array))
            
                if diff < self.config.settings.optimization.static_threshold:
                    frame = prev_frame.copy()
                    logging.debug(f"Frame {frame_idx}: Using previous frame (diff: {diff:.4f})")
        
            return frame
        
        except Exception as e:
            logging.error(f"Frame processing error: {e}")
            traceback.print_exc()
            return frame

class AutoGIFApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        
        # Create app directory structure
        self.app_dir = Path.home() / ".autogif"
        self.app_dir.mkdir(exist_ok=True)
        (self.app_dir / "temp").mkdir(exist_ok=True)
        (self.app_dir / "output").mkdir(exist_ok=True)
        
        # Initialize config
        self.config = ConfigManager(self.app_dir)
        
        # Initialize video processor and GIF renderer
        self.video_processor = VideoProcessor(self.config)
        self.video_processor.app = self
        self.gif_renderer = GIFRenderer(self.config)
        
        # Initialize variables
        self.url_var = tk.StringVar()
        self.start_time_var = tk.StringVar(value="0:00")
        self.end_time_var = tk.StringVar(value="0:10")
        self.fps_var = tk.StringVar(value=str(self.config.settings.fps))
        self.resolution_var = tk.StringVar(value=self.config.settings.resolution)
        self.output_dir_var = tk.StringVar(value=self.config.settings.output_directory)
        self.status_var = tk.StringVar(value="Ready")
        self.loop_var = tk.BooleanVar(value=self.config.settings.loop_gif)
        self.font_name_var = tk.StringVar(value=self.config.settings.font_name)
        self.font_size_var = tk.StringVar(value=str(self.config.settings.font_size))
        
        # Initialize optimization variables
        self.dither_mode_var = tk.StringVar(value=self.config.settings.optimization.dither_mode)
        self.color_limit_var = tk.StringVar(value=str(self.config.settings.optimization.color_limit))
        self.web_safe_var = tk.BooleanVar(value=self.config.settings.optimization.web_safe_colors)
        self.detect_static_var = tk.BooleanVar(value=self.config.settings.optimization.detect_static_frames)
        
        # Initialize effect variables
        self.effect_vars = {}
        
        # Set window title
        root.title(f"AutoGIF v{VERSION}")
        
        # Configure root window
        root.minsize(600, 650)
        root.columnconfigure(0, weight=1)
        root.rowconfigure(0, weight=1)
        
        # Calculate initial window size based on screen dimensions
        screen_width = root.winfo_screenwidth()
        screen_height = root.winfo_screenheight()
        window_width = min(800, int(screen_width * 0.6))
        window_height = min(800, int(screen_height * 0.7))
        
        # Center the window
        x = (screen_width - window_width) // 2
        y = (screen_height - window_height) // 2
        root.geometry(f"{window_width}x{window_height}+{x}+{y}")
        
        # Bind resize event
        root.bind("<Configure>", self.on_window_configure)
        
        # Create UI
        self.create_ui()
        
        # Configure window closing
        root.protocol("WM_DELETE_WINDOW", self.on_closing)

    def create_ui(self):
        """Create the user interface with improved layout and responsiveness"""
        # Add menubar
        self.menubar = tk.Menu(self.root)
        self.root.config(menu=self.menubar)
        
        # Create Settings menu
        self.settings_menu = tk.Menu(self.menubar, tearoff=0)
        self.menubar.add_cascade(label="Settings", menu=self.settings_menu)
        
        # Add Font Settings submenu
        self.font_menu = tk.Menu(self.settings_menu, tearoff=0)
        self.settings_menu.add_cascade(label="Font Settings", menu=self.font_menu)
        self.font_menu.add_command(label="Configure Fonts...", command=self.show_font_settings)
        
        # Add Text Effects submenu
        self.text_effects_menu = tk.Menu(self.settings_menu, tearoff=0)
        self.settings_menu.add_cascade(label="Text Effects", menu=self.text_effects_menu)
        self.text_effects_menu.add_command(
            label="Configure Text Effects...", 
            command=self.show_text_effects_settings
        )

        # Add Optimization submenu
        self.create_optimization_menu()

        # Main frame with proper padding and scaling
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky="nsew")
        main_frame.columnconfigure(0, weight=1)
        main_frame.rowconfigure(3, weight=1)

        # URL Frame with dynamic width
        url_frame = ttk.LabelFrame(main_frame, text="YouTube URL", padding="5")
        url_frame.grid(row=0, column=0, sticky="ew", padx=5, pady=5)
        url_frame.columnconfigure(0, weight=1)

        # URL Entry with paste button
        url_entry = ttk.Entry(url_frame, textvariable=self.url_var)
        url_entry.grid(row=0, column=0, sticky="ew", padx=5)
        
        paste_btn = ttk.Button(url_frame, text="Paste", command=self.paste_url, width=10)
        paste_btn.grid(row=0, column=1, padx=5)

        # Recent URLs dropdown with dynamic width
        self.recent_urls_var = tk.StringVar()
        recent_urls = ttk.Combobox(
            url_frame,
            textvariable=self.recent_urls_var,
            values=self.config.settings.recent_urls,
            state="readonly"
        )
        recent_urls.grid(row=1, column=0, columnspan=2, sticky="ew", padx=5, pady=5)
        recent_urls.bind('<<ComboboxSelected>>', 
                        lambda e: self.url_var.set(self.recent_urls_var.get()))

        time_frame = ttk.LabelFrame(main_frame, text="Time Range", padding="5")
        time_frame.grid(row=1, column=0, sticky="ew", padx=5, pady=5)
        time_frame.columnconfigure(1, weight=1)
        time_frame.columnconfigure(3, weight=1)

        ttk.Label(time_frame, text="Start Time:").grid(row=0, column=0, padx=5)
        ttk.Entry(
            time_frame,
            textvariable=self.start_time_var,
            width=12  # Increased width to accommodate milliseconds
        ).grid(row=0, column=1, sticky="w", padx=5)

        ttk.Label(time_frame, text="End Time:").grid(row=0, column=2, padx=5)
        ttk.Entry(
            time_frame,
            textvariable=self.end_time_var,
            width=12  # Increased width to accommodate milliseconds
        ).grid(row=0, column=3, sticky="w", padx=5)
        
        tooltip_text = "Format: MM:SS.mmm or HH:MM:SS.mmm"
        ttk.Label(time_frame, text=tooltip_text, font=("TkDefaultFont", 8)).grid(
            row=1, column=0, columnspan=4, sticky="w", padx=5, pady=(0,5))

        # Settings Frame
        settings_frame = ttk.LabelFrame(main_frame, text="Settings", padding="5")
        settings_frame.grid(row=2, column=0, sticky="ew", padx=5, pady=5)
        settings_frame.columnconfigure(1, weight=1)

        # FPS setting with validation
        row = 0
        ttk.Label(settings_frame, text="FPS:").grid(row=row, column=0, padx=5, pady=2)
        fps_entry = ttk.Entry(settings_frame, textvariable=self.fps_var, width=10)
        fps_entry.grid(row=row, column=1, sticky="w", padx=5)
        fps_entry.bind('<FocusOut>', lambda e: self.validate_fps())

        # Resolution setting
        row += 1
        ttk.Label(settings_frame, text="Resolution:").grid(row=row, column=0, padx=5, pady=2)
        resolution_combo = ttk.Combobox(
            settings_frame,
            textvariable=self.resolution_var,
            values=self.config.settings.resolutions,
            width=8,
            state="readonly"
        )
        resolution_combo.grid(row=row, column=1, sticky="w", padx=5)

        # Loop GIF checkbox
        row += 1
        ttk.Checkbutton(
            settings_frame,
            text="Loop GIF",
            variable=self.loop_var
        ).grid(row=row, column=0, columnspan=2, sticky="w", padx=5, pady=2)

        # Output directory with browse button
        row += 1
        ttk.Label(settings_frame, text="Output Directory:").grid(
            row=row, column=0, padx=5, pady=2)

        dir_frame = ttk.Frame(settings_frame)
        dir_frame.grid(row=row, column=1, sticky="ew", pady=2)
        dir_frame.columnconfigure(0, weight=1)

        ttk.Entry(dir_frame, textvariable=self.output_dir_var).grid(
            row=0, column=0, sticky="ew", padx=(0, 5))

        ttk.Button(
            dir_frame,
            text="Browse",
            command=self.browse_output_dir,
            width=10
        ).grid(row=0, column=1)

        # Progress Frame with dynamic sizing
        progress_frame = ttk.Frame(main_frame)
        progress_frame.grid(row=3, column=0, sticky="nsew", padx=5, pady=5)
        progress_frame.columnconfigure(0, weight=1)
        progress_frame.rowconfigure(0, weight=1)

        self.progress = ttk.Progressbar(
            progress_frame,
            mode='determinate'
        )
        self.progress.grid(row=0, column=0, sticky="ew", pady=5)

        status_label = ttk.Label(
            progress_frame,
            textvariable=self.status_var,
            wraplength=400
        )
        status_label.grid(row=1, column=0, sticky="w")

        # Button Frame with consistent button sizing
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=4, column=0, sticky="ew", padx=5, pady=5)
        button_frame.columnconfigure(1, weight=1)

        self.create_button = ttk.Button(
            button_frame,
            text="Create GIF",
            command=lambda: threading.Thread(target=self.process_video).start(),
            width=15
        )
        self.create_button.grid(row=0, column=0, padx=5)

        self.cancel_button = ttk.Button(
            button_frame,
            text="Cancel",
            command=self.cancel_operation,
            state='disabled',
            width=15
        )
        self.cancel_button.grid(row=0, column=1, padx=5)

        open_folder_btn = ttk.Button(
            button_frame,
            text="Open Output Folder",
            command=self.open_output_folder,
            width=15
        )
        open_folder_btn.grid(row=0, column=2, padx=5)

    def show_font_settings(self):
        """Show font settings dialog with improved layout and responsiveness"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Font Settings")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Configure dialog
        dialog.minsize(400, 350)
        dialog.resizable(True, True)
        
        # Calculate dialog size based on screen dimensions
        screen_width = dialog.winfo_screenwidth()
        screen_height = dialog.winfo_screenheight()
        width = min(500, int(screen_width * 0.4))
        height = min(450, int(screen_height * 0.4))
        
        # Center the dialog
        x = (screen_width - width) // 2
        y = (screen_height - height) // 2
        dialog.geometry(f"{width}x{height}+{x}+{y}")
        
        # Make dialog resizable
        dialog.columnconfigure(0, weight=1)
        dialog.rowconfigure(0, weight=1)
        
        # Create main frame
        frame = ttk.Frame(dialog, padding="10")
        frame.grid(row=0, column=0, sticky="nsew")
        frame.columnconfigure(1, weight=1)
        
        # Font selection
        ttk.Label(frame, text="Font:").grid(row=0, column=0, sticky="w", pady=5)
        font_combo = ttk.Combobox(
            frame,
            textvariable=self.font_name_var,
            values=self.config.settings.available_fonts,
            width=30,
            state="readonly"
        )
        font_combo.grid(row=0, column=1, columnspan=2, sticky="ew", pady=5)
        
        # Font size
        ttk.Label(frame, text="Font Size:").grid(row=1, column=0, sticky="w", pady=5)
        size_combo = ttk.Combobox(
            frame,
            textvariable=self.font_size_var,
            values=self.config.settings.font_sizes,
            width=8,
            state="readonly"
        )
        size_combo.grid(row=1, column=1, sticky="w", pady=5)
        
        # Color selection
        ttk.Label(frame, text="Font Color:").grid(row=2, column=0, sticky="w", pady=5)
        
        # Color preview frame
        color_preview_frame = ttk.Frame(frame, width=32, height=32)
        color_preview_frame.grid(row=2, column=1, sticky="w", pady=5, padx=(0, 5))
        color_preview_frame.grid_propagate(False)
        
        color_preview = tk.Canvas(
            color_preview_frame,
            width=30,
            height=30,
            bg=self.config.settings.font_color,
            highlightthickness=1,
            highlightbackground="gray"
        )
        color_preview.place(relx=0.5, rely=0.5, anchor="center")
        
        def update_color():
            """Update font color with color picker"""
            from tkinter import colorchooser
            color = colorchooser.askcolor(
                color=self.config.settings.font_color,
                title="Choose Font Color"
            )
            if color[1]:  # color[1] contains the hex value
                self.config.settings.font_color = color[1]
                color_preview.configure(bg=color[1])
                preview_label.configure(foreground=color[1])
        
        color_button = ttk.Button(
            frame,
            text="Choose Color",
            command=update_color,
            width=15
        )
        color_button.grid(row=2, column=2, sticky="w", pady=5)
        
        # Preview frame with scroll region
        preview_frame = ttk.LabelFrame(frame, text="Preview", padding="5")
        preview_frame.grid(row=3, column=0, columnspan=3, sticky="nsew", pady=10)
        preview_frame.columnconfigure(0, weight=1)
        preview_frame.rowconfigure(0, weight=1)

        # Time selection frame
        time_select_frame = ttk.Frame(preview_frame)
        time_select_frame.grid(row=1, column=0, sticky="ew", padx=5, pady=(0, 5))
        time_select_frame.columnconfigure(3, weight=1)
        
        # Start time selection
        ttk.Label(time_select_frame, text="Start:").grid(row=0, column=0, padx=(0, 5))
        self.start_time_var = tk.StringVar(value="0:00")
        self.start_entry = ttk.Entry(time_select_frame, textvariable=self.start_time_var, width=10)
        self.start_entry.grid(row=0, column=1, padx=5)
        self.set_start_btn = ttk.Button(
            time_select_frame,
            text="Set Start",
            command=self.set_start_time,
            width=10,
            style="Green.TButton"
        )
        self.set_start_btn.grid(row=0, column=2, padx=5)
        
        # End time selection
        ttk.Label(time_select_frame, text="End:").grid(row=0, column=4, padx=(20, 5))
        self.end_time_var = tk.StringVar(value="0:00")
        self.end_entry = ttk.Entry(time_select_frame, textvariable=self.end_time_var, width=10)
        self.end_entry.grid(row=0, column=5, padx=5)
        self.set_end_btn = ttk.Button(
            time_select_frame,
            text="Set End",
            command=self.set_end_time,
            width=10,
            style="Red.TButton"
        )
        self.set_end_btn.grid(row=0, column=6, padx=5)

        # Timeline control frame
        timeline_frame = ttk.Frame(preview_frame)
        timeline_frame.grid(row=2, column=0, sticky="ew", padx=5, pady=5)  # Changed from row=1 to row=2
        
        preview_canvas = tk.Canvas(preview_frame, height=100)
        preview_canvas.grid(row=0, column=0, sticky="nsew")
        
        preview_text = "The quick brown fox jumps over the lazy dog\n1234567890"
        preview_label = ttk.Label(
            preview_canvas,
            text=preview_text,
            font=(self.font_name_var.get(), int(self.font_size_var.get())),
            foreground=self.config.settings.font_color,
            background="white"
        )
        preview_window = preview_canvas.create_window(
            0, 0,
            anchor="nw",
            window=preview_label
        )
        
        def update_preview(*args):
            """Update preview text with current settings"""
            try:
                preview_label.configure(
                    font=(self.font_name_var.get(), int(self.font_size_var.get()))
                )
                # Update canvas scrollregion
                preview_canvas.configure(scrollregion=preview_canvas.bbox("all"))
            except Exception as e:
                logging.warning(f"Preview update failed: {e}")
        
        # Bind preview updates
        self.font_name_var.trace_add("write", update_preview)
        self.font_size_var.trace_add("write", update_preview)
        
        # Button frame
        button_frame = ttk.Frame(frame)
        button_frame.grid(row=4, column=0, columnspan=3, pady=20)
        
        def save_settings():
            """Save font settings and close dialog"""
            try:
                self.config.update_settings(
                    font_name=self.font_name_var.get(),
                    font_size=int(self.font_size_var.get())
                )
                self.gif_renderer._load_font()
                dialog.destroy()
            except Exception as e:
                messagebox.showerror("Error", f"Failed to save settings: {str(e)}")
        
        # Save button
        save_button = ttk.Button(
            button_frame,
            text="Save",
            command=save_settings,
            width=15
        )
        save_button.pack(side=tk.LEFT, padx=5)
        
        # Cancel button
        cancel_button = ttk.Button(
            button_frame,
            text="Cancel",
            command=dialog.destroy,
            width=15
        )
        cancel_button.pack(side=tk.LEFT, padx=5)
        
        # Handle window resize
        def on_resize(event):
            if event.widget == dialog:
                # Update preview canvas size
                width = max(event.width - 40, 360)  # 40 pixels for padding
                preview_canvas.configure(width=width)
                
                # Update preview label wraplength
                preview_label.configure(wraplength=width - 20)  # 20 pixels for margins
        
        dialog.bind("<Configure>", on_resize)
        
        # Ensure dialog stays on top and focused
        dialog.lift()
        dialog.focus_force()

    def show_text_effects_settings(self):
        """Show text effects settings dialog"""
        # Create dialog
        effects_dialog = tk.Toplevel(self.root)
        effects_dialog.title("Text Effects Settings")
        effects_dialog.transient(self.root)
        effects_dialog.grab_set()
        
        # Configure dialog
        effects_dialog.geometry("400x700")
        effects_dialog.resizable(False, False)
        
        # Center dialog
        effects_dialog.update_idletasks()
        x = (effects_dialog.winfo_screenwidth() // 2) - (effects_dialog.winfo_width() // 2)
        y = (effects_dialog.winfo_screenheight() // 2) - (effects_dialog.winfo_height() // 2)
        effects_dialog.geometry(f'+{x}+{y}')
        
        # Create main frame first
        main_frame = ttk.Frame(effects_dialog, padding="10")
        main_frame.pack(fill=tk.BOTH, expand=True)
        
        # Create canvas and scrollbar
        canvas = tk.Canvas(main_frame)
        scrollbar = ttk.Scrollbar(main_frame, orient="vertical", command=canvas.yview)
        
        # Create frame for content
        content_frame = ttk.Frame(canvas)
        
        # Configure canvas
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # Pack scrollbar and canvas
        scrollbar.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        
        # Create window in canvas
        canvas_window = canvas.create_window((0, 0), window=content_frame, anchor="nw")
        
        # Configure canvas scrolling
        def configure_canvas(event):
            canvas.configure(scrollregion=canvas.bbox("all"))
            # Ensure the canvas window spans the full width
            canvas.itemconfig(canvas_window, width=canvas.winfo_width())
        
        content_frame.bind('<Configure>', configure_canvas)
        canvas.bind('<Configure>', lambda e: canvas.itemconfig(canvas_window, width=e.width))
        
        # Enable mousewheel scrolling
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        
        # Reset effect variables
        self.effect_vars = {}
        
        # Add global opacity control at the top
        opacity_frame = ttk.LabelFrame(content_frame, text="Global Opacity", padding="5")
        opacity_frame.pack(fill="x", padx=5, pady=5)
        
        opacity_var = tk.IntVar(value=getattr(self.config.settings, 'text_opacity', 100))
        opacity_label = ttk.Label(opacity_frame, text="Text Opacity:")
        opacity_label.pack(side="left", padx=5)
        
        opacity_value_label = ttk.Label(opacity_frame, textvariable=opacity_var)
        opacity_value_label.pack(side="right", padx=5)
        
        opacity_scale = ttk.Scale(
            opacity_frame,
            from_=0,
            to=100,
            variable=opacity_var,
            orient="horizontal"
        )
        opacity_scale.pack(fill="x", expand=True, padx=5)
        
        # Add preview label
        preview_frame = ttk.LabelFrame(content_frame, text="Current Settings", padding="5")
        preview_frame.pack(fill="x", padx=5, pady=5)
        
        preview_label = ttk.Label(
            preview_frame,
            text="No effects currently enabled",
            wraplength=350
        )
        preview_label.pack(fill="x", padx=5, pady=5)
        
        def update_preview(*args):
            """Update preview text with current settings"""
            enabled_effects = []
            for name, vars in self.effect_vars.items():
                if vars['enabled'].get():
                    intensity = vars['intensity'].get()
                    enabled_effects.append(f"{name.title()}: {intensity}%")
            
            if enabled_effects:
                preview_label.configure(
                    text=f"Global Opacity: {opacity_var.get()}%\n\nEnabled effects:\n" + 
                         "\n".join(enabled_effects)
                )
            else:
                preview_label.configure(
                    text=f"Global Opacity: {opacity_var.get()}%\n\nNo effects currently enabled"
                )
        
        # Add trace for opacity preview updates
        opacity_var.trace_add("write", update_preview)
        
        # Create effect controls
        for effect_name, effect_obj in vars(self.config.settings.text_effects).items():
            if not isinstance(effect_obj, TextEffect):
                continue
                
            effect_frame = ttk.LabelFrame(content_frame, text=effect_obj.name, padding="5")
            effect_frame.pack(fill="x", padx=5, pady=5)
            
            # Set up variables with CURRENT values from config
            enabled_var = tk.BooleanVar(value=effect_obj.enabled)
            intensity_var = tk.IntVar(value=effect_obj.intensity)
            
            self.effect_vars[effect_name] = {
                'enabled': enabled_var,
                'intensity': intensity_var,
                'name': effect_obj.name
            }
            
            # Add trace for preview updates
            enabled_var.trace_add("write", update_preview)
            intensity_var.trace_add("write", update_preview)
            
            # Checkbox frame
            cb_frame = ttk.Frame(effect_frame)
            cb_frame.pack(fill="x")
            
            ttk.Checkbutton(
                cb_frame,
                text="Enable",
                variable=enabled_var
            ).pack(side="left")
            
            # Status label - shows actual current state
            status_text = "enabled" if effect_obj.enabled else "disabled"
            status_label = ttk.Label(
                cb_frame,
                text=f"(current: {status_text})"
            )
            status_label.pack(side="left", padx=5)
            
            # Intensity frame
            int_frame = ttk.Frame(effect_frame)
            int_frame.pack(fill="x", pady=5)
            
            ttk.Label(int_frame, text="Intensity:").pack(side="left")
            intensity_label = ttk.Label(
                int_frame,
                text=f"(current: {effect_obj.intensity}%)"
            )
            intensity_label.pack(side="right")
            
            ttk.Scale(
                effect_frame,
                from_=0,
                to=100,
                variable=intensity_var,
                orient="horizontal"
            ).pack(fill="x")
        
        # Initial preview
        update_preview()
        
        # Button frame
        button_frame = ttk.Frame(effects_dialog, padding="10")
        button_frame.pack(fill="x", side="bottom")
        
        def save_settings():
            """Save and apply effect settings"""
            try:
                # Update global opacity
                self.config.settings.text_opacity = opacity_var.get()
                
                # Update effect settings
                for effect_name, vars in self.effect_vars.items():
                    if hasattr(self.config.settings.text_effects, effect_name):
                        effect = getattr(self.config.settings.text_effects, effect_name)
                        enabled = vars['enabled'].get()
                        intensity = vars['intensity'].get()
                        
                        # Log the change
                        logging.info(f"Updating {effect_name}: enabled={enabled}, intensity={intensity}")
                        
                        # Update the effect object
                        effect.enabled = enabled
                        effect.intensity = intensity
                
                # Save to config file
                self.config.save_settings()
                
                # Force reload of GIF renderer to pick up new settings
                self.gif_renderer = GIFRenderer(self.config)
                
                logging.info("Text effect settings saved successfully")
                effects_dialog.destroy()
                
            except Exception as e:
                logging.error(f"Error saving text effect settings: {e}")
                messagebox.showerror("Error", f"Failed to save settings: {str(e)}")
        
        ttk.Button(
            button_frame,
            text="Save",
            command=save_settings
        ).pack(side="left", padx=5)
        
        ttk.Button(
            button_frame,
            text="Cancel",
            command=effects_dialog.destroy
        ).pack(side="right", padx=5)
        
        # Clean up mousewheel binding when dialog closes
        def on_closing():
            canvas.unbind_all("<MouseWheel>")
            effects_dialog.destroy()
        
        effects_dialog.protocol("WM_DELETE_WINDOW", on_closing)

    def create_optimization_menu(self):
        """Create optimization settings submenu"""
        self.optimization_menu = tk.Menu(self.settings_menu, tearoff=0)
        self.settings_menu.add_cascade(label="Optimization", menu=self.optimization_menu)
        
        # Add configuration options
        self.optimization_menu.add_command(
            label="Frame Timing...",
            command=self.show_frame_timing_dialog
        )
        self.optimization_menu.add_command(
            label="Color Settings...",
            command=self.show_color_settings_dialog
        )
        self.optimization_menu.add_command(
            label="Motion Regions...",
            command=self.show_motion_regions_dialog
        )

    def show_frame_timing_dialog(self):
        """Dialog for frame timing settings"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Frame Timing Settings")
        dialog.transient(self.root)
        dialog.grab_set()
        
        frame = ttk.Frame(dialog, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # Default durations
        ttk.Label(frame, text="Default Duration (s):").grid(row=0, column=0, sticky="w")
        default_dur = tk.StringVar(value=str(self.config.settings.optimization.default_duration))
        ttk.Entry(frame, textvariable=default_dur, width=10).grid(row=0, column=1, padx=5)
        
        # Pause duration
        ttk.Label(frame, text="Pause Duration (s):").grid(row=1, column=0, sticky="w")
        pause_dur = tk.StringVar(value=str(self.config.settings.optimization.pause_duration))
        ttk.Entry(frame, textvariable=pause_dur, width=10).grid(row=1, column=1, padx=5)
        
        # Static frame detection
        detect_static = tk.BooleanVar(value=self.config.settings.optimization.detect_static_frames)
        ttk.Checkbutton(
            frame,
            text="Detect Static Frames",
            variable=detect_static
        ).grid(row=2, column=0, columnspan=2, sticky="w")
        
        # Static frame threshold
        ttk.Label(frame, text="Static Threshold:").grid(row=3, column=0, sticky="w")
        threshold_var = tk.StringVar(value=str(self.config.settings.optimization.static_threshold))
        ttk.Entry(frame, textvariable=threshold_var, width=10).grid(row=3, column=1, padx=5)
        
        def save_settings():
            try:
                self.config.settings.optimization.default_duration = float(default_dur.get())
                self.config.settings.optimization.pause_duration = float(pause_dur.get())
                self.config.settings.optimization.detect_static_frames = detect_static.get()
                self.config.settings.optimization.static_threshold = float(threshold_var.get())
                self.config.save_settings()
                dialog.destroy()
            except ValueError as e:
                messagebox.showerror("Error", "Please enter valid numbers")
        
        ttk.Button(frame, text="Save", command=save_settings).grid(row=4, column=0, pady=10)
        ttk.Button(frame, text="Cancel", command=dialog.destroy).grid(row=4, column=1, pady=10)
        
        # Center dialog on screen
        dialog.update_idletasks()
        width = dialog.winfo_width()
        height = dialog.winfo_height()
        x = (dialog.winfo_screenwidth() // 2) - (width // 2)
        y = (dialog.winfo_screenheight() // 2) - (height // 2)
        dialog.geometry(f'+{x}+{y}')
        
        # Ensure dialog stays on top and focused
        dialog.lift()
        dialog.focus_force()

        ttk.Label(frame, text="Static Threshold:").grid(row=3, column=0, sticky="w")
        threshold_var = tk.StringVar(value=str(self.config.settings.optimization.static_threshold))
        ttk.Entry(frame, textvariable=threshold_var, width=10).grid(row=3, column=1, padx=5)
        
        def save_settings():
            try:
                self.config.settings.optimization.default_duration = float(default_dur.get())
                self.config.settings.optimization.pause_duration = float(pause_dur.get())
                self.config.settings.optimization.detect_static_frames = detect_static.get()
                self.config.settings.optimization.static_threshold = float(threshold_var.get())
                self.config.save_settings()
                dialog.destroy()
            except ValueError as e:
                messagebox.showerror("Error", "Please enter valid numbers")
        
        ttk.Button(frame, text="Save", command=save_settings).grid(row=4, column=0, pady=10)
        ttk.Button(frame, text="Cancel", command=dialog.destroy).grid(row=4, column=1, pady=10)

    def show_color_settings_dialog(self):
        """Dialog for color optimization settings"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Color Settings")
        dialog.transient(self.root)
        dialog.grab_set()
        
        frame = ttk.Frame(dialog, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # Dithering mode
        ttk.Label(frame, text="Dithering:").grid(row=0, column=0, sticky="w")
        dither_combo = ttk.Combobox(
            frame,
            textvariable=self.dither_mode_var,
            values=["NONE", "FLOYDSTEINBERG", "ORDERED"],
            state="readonly"
        )
        dither_combo.grid(row=0, column=1, padx=5)
        
        # Color limit
        ttk.Label(frame, text="Color Limit:").grid(row=1, column=0, sticky="w")
        ttk.Entry(frame, textvariable=self.color_limit_var, width=10).grid(row=1, column=1, padx=5)
        
        # Web safe colors
        ttk.Checkbutton(
            frame,
            text="Use Web Safe Colors",
            variable=self.web_safe_var
        ).grid(row=2, column=0, columnspan=2, sticky="w")
        
        def save_settings():
            try:
                self.config.settings.optimization.dither_mode = self.dither_mode_var.get()
                self.config.settings.optimization.color_limit = int(self.color_limit_var.get())
                self.config.settings.optimization.web_safe_colors = self.web_safe_var.get()
                self.config.save_settings()
                dialog.destroy()
            except ValueError as e:
                messagebox.showerror("Error", "Please enter a valid number for color limit")
        
        ttk.Button(frame, text="Save", command=save_settings).grid(row=4, column=0, pady=10)
        ttk.Button(frame, text="Cancel", command=dialog.destroy).grid(row=4, column=1, pady=10)

    def show_motion_regions_dialog(self):
        """Dialog for managing motion regions"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Motion Regions")
        dialog.transient(self.root)
        dialog.grab_set()
        
        frame = ttk.Frame(dialog, padding="10")
        frame.pack(fill=tk.BOTH, expand=True)
        
        # List of current regions
        regions_frame = ttk.LabelFrame(frame, text="Defined Regions", padding="5")
        regions_frame.pack(fill=tk.BOTH, expand=True)
        
        regions_list = tk.Listbox(regions_frame, height=5)
        regions_list.pack(fill=tk.BOTH, expand=True)
        
        # Update regions list
        def update_regions_list():
            regions_list.delete(0, tk.END)
            for i, region in enumerate(self.config.settings.optimization.motion_regions):
                regions_list.insert(tk.END, f"Region {i+1}: ({region.x1},{region.y1}) to ({region.x2},{region.y2})")
        
        update_regions_list()
        
        # Add new region
        def add_region():
            try:
                region = MotionRegion(0, 0, 100, 100)  # Default size
                self.config.settings.optimization.motion_regions.append(region)
                update_regions_list()
            except Exception as e:
                messagebox.showerror("Error", str(e))
        
        # Remove selected region
        def remove_region():
            selection = regions_list.curselection()
            if selection:
                idx = selection[0]
                del self.config.settings.optimization.motion_regions[idx]
                update_regions_list()
        
        # Edit selected region
        def edit_region():
            selection = regions_list.curselection()
            if not selection:
                return
                
            idx = selection[0]
            region = self.config.settings.optimization.motion_regions[idx]
            
            edit_dialog = tk.Toplevel(dialog)
            edit_dialog.title(f"Edit Region {idx+1}")
            edit_dialog.transient(dialog)
            edit_dialog.grab_set()
            
            edit_frame = ttk.Frame(edit_dialog, padding="10")
            edit_frame.pack(fill=tk.BOTH, expand=True)
            
            # Coordinates
            ttk.Label(edit_frame, text="X1:").grid(row=0, column=0)
            x1_var = tk.StringVar(value=str(region.x1))
            ttk.Entry(edit_frame, textvariable=x1_var, width=6).grid(row=0, column=1)
            
            ttk.Label(edit_frame, text="Y1:").grid(row=0, column=2)
            y1_var = tk.StringVar(value=str(region.y1))
            ttk.Entry(edit_frame, textvariable=y1_var, width=6).grid(row=0, column=3)
            
            ttk.Label(edit_frame, text="X2:").grid(row=1, column=0)
            x2_var = tk.StringVar(value=str(region.x2))
            ttk.Entry(edit_frame, textvariable=x2_var, width=6).grid(row=1, column=1)
            
            ttk.Label(edit_frame, text="Y2:").grid(row=1, column=2)
            y2_var = tk.StringVar(value=str(region.y2))
            ttk.Entry(edit_frame, textvariable=y2_var, width=6).grid(row=1, column=3)
            
            # Options
            enabled_var = tk.BooleanVar(value=region.enabled)
            ttk.Checkbutton(
                edit_frame,
                text="Enabled",
                variable=enabled_var
            ).grid(row=2, column=0, columnspan=2)
            
            fade_var = tk.BooleanVar(value=region.fade_edges)
            ttk.Checkbutton(
                edit_frame,
                text="Fade Edges",
                variable=fade_var
            ).grid(row=2, column=2, columnspan=2)
            
            def save_region():
                try:
                    region.x1 = int(x1_var.get())
                    region.y1 = int(y1_var.get())
                    region.x2 = int(x2_var.get())
                    region.y2 = int(y2_var.get())
                    region.enabled = enabled_var.get()
                    region.fade_edges = fade_var.get()
                    update_regions_list()
                    edit_dialog.destroy()
                except ValueError:
                    messagebox.showerror("Error", "Please enter valid numbers")
            
            ttk.Button(edit_frame, text="Save", command=save_region).grid(row=3, column=0, columnspan=2, pady=5)
            ttk.Button(edit_frame, text="Cancel", command=edit_dialog.destroy).grid(row=3, column=2, columnspan=2, pady=5)
        
        # Buttons
        button_frame = ttk.Frame(frame)
        button_frame.pack(fill=tk.X, pady=5)
        
        ttk.Button(button_frame, text="Add Region", command=add_region).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Edit Selected", command=edit_region).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Remove Selected", command=remove_region).pack(side=tk.LEFT, padx=5)
        ttk.Button(button_frame, text="Close", command=dialog.destroy).pack(side=tk.RIGHT, padx=5)

    def paste_url(self):
        """Paste URL from clipboard"""
        try:
            url = self.root.clipboard_get()
            self.url_var.set(url)
        except:
            pass

    def browse_output_dir(self):
        """Browse for output directory"""
        directory = filedialog.askdirectory(
            initialdir=self.output_dir_var.get() or str(self.app_dir / "output")
        )
        if directory:
            self.output_dir_var.set(directory)
            self.config.update_settings(output_directory=directory)

    def add_recent_url(self, url: str):
        """Add URL to recent URLs list"""
        recent_urls = self.config.settings.recent_urls
        if url in recent_urls:
            recent_urls.remove(url)
        recent_urls.insert(0, url)
        if len(recent_urls) > self.config.settings.max_recent_urls:
            recent_urls = recent_urls[:self.config.settings.max_recent_urls]
        self.config.settings.recent_urls = recent_urls
        self.config.save_settings()

    def parse_time(self, time_str: str) -> float:
        """Parse time string (MM:SS.mmm or HH:MM:SS.mmm) to seconds"""
        try:
            parts = time_str.split(':')
            if len(parts) == 2:  # MM:SS.mmm
                minutes, seconds = parts
                return float(minutes) * 60 + float(seconds)
            elif len(parts) == 3:  # HH:MM:SS.mmm
                hours, minutes, seconds = parts
                return float(hours) * 3600 + float(minutes) * 60 + float(seconds)
            raise ValueError
        except:
            raise ValueError("Invalid time format. Use MM:SS.mmm or HH:MM:SS.mmm")

    def open_output_folder(self):
        """Open output directory in file explorer"""
        output_dir = self.output_dir_var.get() or str(self.app_dir / "output")
        if platform.system() == "Windows":
            os.startfile(output_dir)
        elif platform.system() == "Darwin":
            subprocess.run(["open", output_dir])
        else:
            subprocess.run(["xdg-open", output_dir])

    def on_window_configure(self, event):
        """Handle window resize events"""
        if event.widget == self.root:
            # Enforce minimum window size
            if event.width < 600:
                self.root.geometry(f"600x{event.height}")
            if event.height < 650:
                self.root.geometry(f"{event.width}x650")
            
            # Update progress bar width
            self.progress.configure(length=event.width - 50)

    def validate_fps(self):
        """Validate FPS input"""
        try:
            fps = int(self.fps_var.get())
            if fps < 1:
                self.fps_var.set("1")
            elif fps > 30:
                self.fps_var.set("30")
        except ValueError:
            self.fps_var.set("10")  # Reset to default if invalid

    def update_status(self, message: str, progress: float = None):
        """Update status message and progress bar"""
        self.status_var.set(message)
        if progress is not None:
            self.progress['value'] = progress
        self.root.update_idletasks()
        
        # Ensure window remains responsive during long operations
        self.root.update()

    def focus_window(self):
        """Ensure main window has focus"""
        self.root.lift()
        self.root.focus_force()

    def process_video(self):
        """Process video and create GIF"""
        try:
            # Validate inputs
            url = self.url_var.get().strip()
            if not url:
                raise ValueError("Please enter a YouTube URL")

            # Parse times with millisecond precision
            start_time = self.parse_time(self.start_time_var.get())
            end_time = self.parse_time(self.end_time_var.get())
            duration = end_time - start_time
        
            if duration <= 0:
                raise ValueError("End time must be after start time")
        
            if duration > 60:
                raise ValueError("Maximum duration is 60 seconds")

            # Validate FPS
            try:
                fps = int(self.fps_var.get())
                if not 1 <= fps <= 30:
                    raise ValueError
            except:
                raise ValueError("FPS must be between 1 and 30")

            # Update font settings
            font_name = self.font_name_var.get()
            font_size = int(self.font_size_var.get())
            self.config.update_settings(
                font_name=font_name,
                font_size=font_size,
                resolution=self.resolution_var.get(),
                fps=fps,
                loop_gif=self.loop_var.get()
            )
            self.gif_renderer._load_font()

            # Prepare UI
            self.create_button.configure(state='disabled')
            self.cancel_button.configure(state='normal')
            self.video_processor.cancel_flag = False

            # Add URL to recent list
            self.add_recent_url(url)

            # Create output filename
            output_dir = self.output_dir_var.get() or str(self.app_dir / "output")
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")[:19]  # Include milliseconds in filename
            output_path = os.path.join(output_dir, f"gif_{timestamp}.gif")

            # Process video with precise timing
            self.update_status("Downloading video segment...")
            video_path = self.video_processor.download_segment(url, start_time, duration)

            # Extract audio and generate subtitles
            audio_path = self.video_processor.extract_audio(video_path)
            segments = self.video_processor.generate_subtitles(audio_path)

            # Open caption editor with video path, config and gif renderer
            self.update_status("Editing captions...")
            editor = CaptionEditor(
                parent=self.root,
                segments=segments,
                video_path=video_path,
                config=self.config,
                gif_renderer=self.gif_renderer
            )
            self.root.wait_window(editor)
        
            if editor.edited_segments is not None:
                segments = editor.edited_segments
                # Use the exact cut times from the editor
                start_time = editor.final_start_time
                end_time = editor.final_end_time
                duration = end_time - start_time
                
                logging.debug(f"Processing video with start: {start_time:.3f}s, end: {end_time:.3f}s")
                
                # Adjust segment times relative to new start time
                adjusted_segments = []
                for segment in segments:
                    # Only include segments that overlap with our time range
                    if segment.end_time <= start_time or segment.start_time >= end_time:
                        continue
                    
                    adjusted_segments.append(VideoSegment(
                        start_time=max(0, segment.start_time - start_time),
                        end_time=min(duration, segment.end_time - start_time),
                        text=segment.text
                    ))
                
                segments = adjusted_segments

            # Create GIF with precise timing
            self.update_status("Creating GIF...")
            self.video_processor.create_gif(video_path, output_path, fps, segments)

            # Clean up
            try:
                os.remove(video_path)
                os.remove(audio_path)
            except Exception as e:
                logging.warning(f"Cleanup error: {e}")

            # Auto-open output folder
            if self.config.settings.auto_open_folder:
                self.open_output_folder()

            messagebox.showinfo("Success", "GIF created successfully!")

        except Exception as e:
            logging.error(f"Processing error: {str(e)}")
            messagebox.showerror("Error", str(e))
            self.update_status("Ready")

        finally:
            self.create_button.configure(state='normal')
            self.cancel_button.configure(state='disabled')
            self.progress['value'] = 0

    def cancel_operation(self):
        """Cancel current operation"""
        self.video_processor.cancel_flag = True
        self.update_status("Cancelling...")
        self.cancel_button.configure(state='disabled')

    def on_closing(self):
        """Handle window closing"""
        try:
            self.video_processor.cancel_flag = True
            
            # Clean up processors
            self.video_processor.cleanup()
            self.gif_renderer.cleanup()
            
            # Clean up temp directory
            temp_dir = self.app_dir / "temp"
            for file in temp_dir.glob("*"):
                try:
                    file.unlink()
                    logging.debug(f"Cleaned up: {file}")
                except Exception as e:
                    logging.warning(f"Failed to clean up {file}: {e}")
                    
        except Exception as e:
            logging.error(f"Cleanup error: {e}")
        finally:
            self.root.destroy()

def main():
    try:
        # Configure logging
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(levelname)s - %(message)s'
        )
        logging.info(f"Starting AutoGIF v{VERSION}")
        
        # Create the root window
        root = tk.Tk()
        root.title(f"AutoGIF v{VERSION}")
        
        # Create the app instance with root
        app = AutoGIFApp(root)
        
        # Start the main loop
        root.mainloop()
        
    except Exception as e:
        logging.error(f"Unhandled exception: {e}", exc_info=True)
        messagebox.showerror(
            "Error",
            f"An unhandled error occurred:\n{str(e)}\n\n"
            "Please check the log file for details."
        )

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        with open('error_log.txt', 'w') as f:
            f.write(f"Error: {str(e)}\n")
            f.write(traceback.format_exc())
        input("Press Enter to exit...")
        sys.exit(1)
