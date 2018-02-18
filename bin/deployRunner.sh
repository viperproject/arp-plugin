#!/bin/sh
cd /home/developer/source/arp-plugin/
sbt assembly
cp target/scala-2.11/arp-plugin.jar ../viper-runner/fatjars/silicon-base.jar
cd /home/developer/source/arp-plugin-carbon/
sbt assembly
cp target/scala-2.11/arp-plugin.jar ../viper-runner/fatjars/carbon-base.jar
