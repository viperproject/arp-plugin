#!/bin/sh
cd /home/developer/source/arp-plugin/
sbt assembly
cp target/scala-2.11/arp-plugin.jar ../viper-runner/fatjars/silicon-base.jar
cp target/scala-2.11/arp-plugin.jar ../../nagini/backends/silicon.jar
cd /home/developer/source/arp-plugin-carbon/
sbt assembly
cp target/scala-2.11/arp-plugin.jar ../viper-runner/fatjars/carbon-base.jar
cp target/scala-2.11/arp-plugin.jar ../../nagini/backends/carbon.jar
