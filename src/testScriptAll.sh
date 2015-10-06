#!/bin/bash
 make && ./proverif -in pitype -ukano ./examples/pace.pi && ./proverif -in pitype OUTPUT_C2.pi &&
 ./proverif -in pitype -ukano ./examples/full_passport_eq.pi && ./proverif -in pitype OUTPUT_C2.pi &&
 ./proverif -in pitype -ukano ./examples/aka.pi && ./proverif -in pitype OUTPUT_C2.pi

