# -*- mode: python ; coding: utf-8 -*-
import os
import sys
from pathlib import Path
import whisper
block_cipher = None
# Get the path to ffmpeg
if sys.platform == "win32":
    ffmpeg_path = 'C:\\ProgramData\\chocolatey\\bin\\ffmpeg.exe'
else:
    ffmpeg_path = '/usr/bin/ffmpeg'
# Get Whisper assets path
whisper_path = os.path.dirname(whisper.__file__)
assets_path = os.path.join(whisper_path, 'assets')
a = Analysis(
    ['AutoGIF.py'],
    pathex=[],
    binaries=[
        (ffmpeg_path, '.') if os.path.exists(ffmpeg_path) else None,
    ],
    datas=[
        (whisper_path, 'whisper'),
        (assets_path, 'whisper/assets'),  # Include Whisper assets
    ],
    hiddenimports=[
        'numpy',
        'numpy.core.multiarray',
        'numpy.random',  # For random effects
        'numpy.linalg',  # For transform matrices
        'yt_dlp',
        'whisper',
        'torch',
        'PIL',
        'PIL.ImageDraw',  # For text rendering
        'PIL.ImageFont',  # For font handling
        'PIL.ImageEnhance',  # For effect enhancements
        'PIL.ImageColor',  # For color handling
        'PIL.ImageTk',    # For preview display
        'cv2',
        'cv2.gapi',  # For advanced image processing
        'tkinter',
        'tkinter.ttk',  # For modern widgets
        'tkinter.scrolledtext',  # For scrollable text areas
        'tkinter.filedialog',  # For file dialogs
        'tkinter.messagebox',  # For message boxes
        'imageio',
        'logging',
        'json',
        'dataclasses',
        'typing',
        'platform',
        'urllib.parse',
        'torch.nn',
        'torch.nn.functional',
        'torch.optim',
        'math',  # For effect calculations
        'random',  # For random effect variations
        'enum',  # For effect enums
        'tempfile',  # For temporary file handling
        'threading',  # For background processing
        're',  # For text processing
        'datetime',  # For timestamp generation
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=block_cipher,
    noarchive=False,
)
# Remove any None entries from binaries
a.binaries = [b for b in a.binaries if b is not None]
pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)
exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.zipfiles,
    a.datas,
    [],
    name='AutoGIF',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,
    disable_windowed_traceback=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    icon='icon.ico' if os.path.exists('icon.ico') else None,
)