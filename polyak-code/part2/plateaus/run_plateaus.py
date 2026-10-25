"""Theorem 10.16: runs verify_plateaus.py on all thirty-five rows of Table 2.

Usage:  python3 run_plateaus.py [--jobs N]

Each row is verified in its own process; the log of a row is written to verification/plateaus/. Three rows
use concavity intervals of radius 0.005 around the atoms instead of 0.015. The program prints one line per
row and exits with status 1 if a row is not verified.
"""
import argparse
import concurrent.futures
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROWS = ['9/37', '7/29', '6/25', '5/21', '9/38', '4/17', '7/30', '5/22', '7/31', '2/9', '5/23', '6/29', '7/34',
        '3/13', 'K3:3/10', 'K3:2/7', 'K3:5/16', 'K3:6/19', 'K3:5/18', 'K5:3/16', 'K5:2/11', 'K5:4/21',
        'K5:5/26', 'K5:7/36', 'K5:4/23', 'K6:3/19', 'K6:2/13', 'K6:5/31', 'K6:4/27', 'K4:3/14', 'K4:4/19',
        'K4:8/39', 'K4:5/24', 'K4:7/33', 'K4:8/33']
NARROW = {'K4:5/24', 'K4:7/33', 'K4:8/33'}


def verify(row):
    cmd = [sys.executable, str(HERE / 'verify_plateaus.py'), str(HERE / 'plateaus_cases.json'), row]
    if row in NARROW:
        cmd.append('5')
    proc = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
    lines = proc.stdout.strip().splitlines()
    last = lines[-1] if lines else ''
    return row, proc.returncode == 0 and 'VERIFIED:' in last and 'NOT VERIFIED' not in last, last


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if len(ROWS) != 35 or len(set(ROWS)) != 35:
        sys.exit('the list of rows is not the table')
    failed = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        for row, ok, last in pool.map(verify, ROWS):
            print(('OK    ' if ok else 'FAIL  ') + last, flush=True)
            if not ok:
                failed.append(row)
    if failed:
        print('NOT VERIFIED:', ', '.join(failed))
        sys.exit(1)
    print('ALL 35 PLATEAUS VERIFIED')


if __name__ == '__main__':
    main()
