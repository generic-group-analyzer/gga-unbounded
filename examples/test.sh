#!/bin/sh

for file in Automatic/*.ubt; do
  printf "$file: \n  "; timeout 120 ../ubt.native $file automatic | tail -1
done
