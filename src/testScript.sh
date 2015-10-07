#!/bin/bash
 make && 
 echo "TESTING full_passport_eq:";
 ./proverif -in pitype -ukano ./examples/full_passport_eq.pi
 echo "Cannot prove:";
 ./proverif -in pitype OUTPUT_C2.pi | grep cannot
 echo "False:";
 ./proverif -in pitype OUTPUT_C2.pi | grep false
 echo "True:";
 ./proverif -in pitype OUTPUT_C2.pi | grep true
