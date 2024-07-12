#!/bin/bash
agda "$1" > /dev/null 2>&1
if [ $? -eq 0 ]; then
    echo "File $1 checked successfully!"
else
    echo "There was an error checking $1"
    agda "$1"
fi