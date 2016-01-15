#!/bin/sh

for file in Automatic/*.ubt; do
  printf "$file: \n  "; timeout 120 ../ubt.native $file | tail -1
done
