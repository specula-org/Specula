#!/bin/bash
# Remaining runs, one at a time, so a batch cannot exhaust the account's usage window.
cd "$(dirname "$0")"
python3 run.py run A2,A3 V03,V02,V01 --jobs 1
python3 run.py run A0,A1 V01,V02 --jobs 1
