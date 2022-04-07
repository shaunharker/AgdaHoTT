#!/bin/bash

rm -rf html
cd src
rm *.agdai
agda --html --html-dir=html --html-highlight=auto -i. index.agda
cd ..
mv ./src/html ./html
