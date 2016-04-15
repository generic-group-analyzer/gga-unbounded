#!/bin/bash

function tests() {
    for file in Automatic/*.ubt; do
        printf "$file:\n";
        before=$(date +%s)
        output=$(timeout 120 ../ubt.native $file | tail -2)
        after=$(date +%s)
        dt=$((after - before))
        if echo $output | grep -q Proven; then
            printf " Proven. Time: \e[1;32m$dt seconds\e[1;0m\n"
        else
            printf " Not proven. Time: \e[1;31m$dt seconds\e[1;0m\n"
        fi  
    done
}

tests
