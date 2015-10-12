#!/bin/bash
 make && 
 echo "################### TESTING PACE (grep 'cannot):"
 ./proverif -in pitype -ukano ./examples/pace.pi && ./proverif -in pitype OUTPUT_C2.pi | grep cannot
 echo "################### TESTING full_passport_eq (grep 'cannot):"
 ./proverif -in pitype -ukano ./examples/full_passport_eq.pi && ./proverif -in pitype OUTPUT_C2.pi | grep cannot
 echo "################### TESTING AKA (grep 'cannot):"
 ./proverif -in pitype -ukano ./examples/AKA.pi && ./proverif -in pitype OUTPUT_C2.pi | grep cannot

