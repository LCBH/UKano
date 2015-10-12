#!/bin/bash
 make && 
 echo "TESTING full_passport_eq:";
 ./proverif -in pitype -ukano ./examples/full_passport_eq.pi
 echo "########## FIRST CONDITION:"
 ./proverif -in pitype ./examples/full_passport_eq_C1.pi
 echo "########## SECOND CONDITION:"
 echo "Cannot prove:";
 ./proverif -in pitype ./examples/full_passport_eq_C2.pi | grep cannot
 echo "False:";
 ./proverif -in pitype ./examples/full_passport_eq_C2.pi | grep false
 echo "True:";
 ./proverif -in pitype ./examples/full_passport_eq_C2.pi | grep true
