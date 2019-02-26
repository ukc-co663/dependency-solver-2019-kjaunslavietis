#/!bin/bash
rm -rf "lib/*"
mkdir -p "lib"
wget -O lib/fastjson-1.2.45.jar http://search.maven.org/remotecontent?filepath=com/alibaba/fastjson/1.2.45/fastjson-1.2.45.jar
wget -O lib/logicng-1.4.1.jar https://search.maven.org/remotecontent?filepath=org/logicng/logicng/1.4.1/logicng-1.4.1.jar

