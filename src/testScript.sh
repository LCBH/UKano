#!/bin/bash
 make && 
 echo "TESTING PACE (grep 'cannot):";
 ./proverif -in pitype -ukano ./examples/pace.pi && ./proverif -in pitype OUTPUT_C2.pi | grep cannot
