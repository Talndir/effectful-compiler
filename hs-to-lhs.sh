#!/bin/bash
file="out/${1%.hs}.lhs"

echo '%include polycode.fmt' > $file
echo '\begin{code}' >> $file
sed -e 's/-- <\(.*\)/\\end{code}\n%<\1\n\\begin{code}/' $1 >> $file
echo -e '\n\\end{code}' >> $file
