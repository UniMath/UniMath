#!/bin/bash
file_name=~/experiments/lang_agent/huggingface/unimath/batch1/proof_trace_log.txt
current_time=$(date "+%Y.%m.%d-%H.%M.%S")
new_fileName=$file_name.$current_time
echo building $new_fileName
make > $new_fileName  2>&1
tail $new_fileName  | grep Error: -B1
