from pathlib import Path
import sys
Path(sys.argv[1]).write_bytes(Path('/workspace/out/negative-controls/enabled.jsonl').read_bytes())
raise SystemExit(42)
