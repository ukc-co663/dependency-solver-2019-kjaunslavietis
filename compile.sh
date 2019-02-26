#!/bin/bash
set -x
CLASSPATH=classes:$(ls lib/* | sed 's/ /:/')
echo $CLASSPATH
mkdir -p classes
javac -cp "lib/*" -sourcepath src/main/java src/main/java/depsolver/Main.java
#javac -sourcepath src/main/java -d classes $JAVAS
