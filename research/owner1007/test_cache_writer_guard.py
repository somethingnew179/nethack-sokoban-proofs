#!/usr/bin/env python3
"""Exercise the real checker while a separate process owns a scratch lock."""
import fcntl
import json
from pathlib import Path
import subprocess
import sys
import tempfile

checker = Path(__file__).with_name('selective_check.py')
with tempfile.TemporaryDirectory(prefix='nethack-owner1007-guard-', dir='/private/tmp') as scratch:
    cache = Path(scratch)
    with (cache/'.writer.lock').open('a+') as owner:
        fcntl.flock(owner.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        command = [sys.executable, str(checker), 'Owner1007.TokenAccounting', '--cache', str(cache)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=10)
        assert result.returncode == 73, (result.returncode, result.stdout, result.stderr)
        assert not (cache/'records.json').exists()
        assert not (cache/'oleans').exists()
        print(json.dumps(dict(status='PASS', command=command, wrapper_exit=0,
                              guarded_child_exit=73, no_receipts_or_oleans_written=True,
                              result=json.loads(result.stdout)), indent=2))
