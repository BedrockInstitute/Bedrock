"""Report Bedrock's Agda source metrics using the shared text counter."""
from pathlib import Path
from outcrop.core.source_metrics import main

if __name__ == '__main__':
    main(default_source=Path(__file__).resolve().parents[2] / 'src')
