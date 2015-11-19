#!/bin/bash

echo "Usage:    './AutoCheck.sh <filename>.pi'                                        "
echo "This script uses the tool UKano to automatically translate 2-agents protocols   "
echo "specified in a ProVerif file into two ProVerif files checking respectively Frame"
echo "opacity and Well-Authentication. The script then launch ProVerif on those files "
echo "and fetch the result of the verification. For more details about the expected   "
echo "file, type './proverif -ukano help'.                                            "

# Modify this if needed:
PRO=./../proverif
FILE=$1
# end

NAME=`echo "$1" | cut -d'.' -f1`
EXTENSION=`echo "$1" | cut -d'.' -f2`
FO_SU=_FOpa.pi
WA_SU=_WAuth.pi
FILE_FO=$NAME$FO_SU
FILE_WA=$NAME$WA_SU

echo ""
echo "## Loading your file and translating...                                          "
$PRO -ukano $FILE

echo "Created files: $FILE_FO, $FILE_WA."


echo ""
echo "If the translations went well, two new files have been created in the same      "
echo "folder as your input file. They are suffixed repsectively by 'FOpa.pi' (checking"
echo "frame opacity) and 'WAuth.pi' (checking well-authentication).                   "
echo "If some warnings about idealization were displayed, you should check that the   "
echo "tool guessed idealizations correctly. If not, you should help him by adding     "
echo "holes. See the UKano's help message for more details.                           "

echo ""
echo "## Checking Frame Opacity...                                                     "
$PRO -in pitype $FILE_FO | grep -E "RESULT"

echo ""
echo "## Checking Well Authentication...                                               "
$PRO -in pitype $FILE_WA | grep -E "RESULT"

echo ""
echo "If all checks went well, your protocol is unlinkable and ensure anonymity w.r.t."
echo "session names prefixed by 'id'.                                                 "