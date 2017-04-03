#!/bin/bash

#Call common buildscript
sh /proj/SMACK/scripts/smackbench_compute_common_buildscript.sh

export DEBIAN_FRONTEND=noninteractive

#Create directory for smack, clone smack, 
#checkout develop and enter dir
mkdir -p /mnt/local/smack-project
cd /mnt/local/smack-project
git clone https://github.com/smackers/smack.git
cd smack/bin
#git checkout svcomp2016
git checkout develop
#git checkout llvm-3.7 
#git checkout svcomp2017
#git checkout avoid-mem-safety-region-collapse

#Build SMACK (using 64 processors during call to make)
sed -i 's/^  make$/  make -j 64/g' build.sh
sed -i 's/^  sudo make install$/  sudo make install -j 64/g' build.sh
./build.sh

#Set up boot script to start on reboot
#sudo bash -c "echo -e \"su -c '. /mnt/local/smack-project/smack.environment && cd /proj/SMACK/SMACKBenchResults && ./runServer.sh' mcarter &\" >> /etc/rc.local"

#Copy console log of this script off ephemeral storage
cp /tmp/smackbench_compute_build.out /mnt/local/

#Reboot
sudo reboot now

