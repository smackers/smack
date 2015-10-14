#!/bin/bash

#Install htop
sudo apt-get update
sudo apt-get install htop -y
sudo apt-get install openjdk-7-jre

#Set permissions on local ephemeral storage,
#so sudo is not needed
sudo chgrp SMACK /mnt/local
sudo chmod g+w /mnt/local

#Create directory for smack, clone smack, 
#checkout develop and enter dir
mkdir -p /mnt/local/smack-project
cd /mnt/local/smack-project
git clone https://github.com/smackers/smack.git
cd smack/bin
git checkout svcomp2016

#Make sure add-apt-repository is installed
sudo apt-get update
sudo apt-get install software-properties-common -y

#Build SMACK (using 64 processors during call to make)
sed -i 's/^  make$/  make -j 64/g' build.sh
sed -i 's/^  sudo make install$/  sudo make install -j 64/g' build.sh
./build.sh

#Install cgroup support
sudo apt-get install cgroup-bin cgroup-lite cgmanager -y

#Enable tracking of memory swapping for processes (requires reboot)
sudo sed -i '/GRUB_CMDLINE_LINUX=/ s/^\(.*\)\("\)/\1 swapaccount=1\2/' /etc/default/grub
sudo update-grub

#Set up boot script to start on reboot
sudo bash -c "echo -e \"su -c '. /mnt/local/smack-project/smack.environment && cd /proj/SMACK/SMACKBenchResults && ./runServer.sh' mcarter &\" >> /etc/rc.local"

#Upgrade kernel
sudo apt-get install --install-recommends linux-generic-lts-vivid -y

#And all packages
sudo apt-get update
sudo apt-get upgrade -y
sudo apt-get update
sudo apt-get upgrade -y

#Reboot
sudo reboot now

