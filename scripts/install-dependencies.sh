#!/bin/sh

# download GNAT Community 2018
wget http://mirrors.cdn.adacore.com/art/5b0d7bffa3f5d709751e3e04 -O gnat-community-2018

# download script to install GNAT Community 2018
git clone https://github.com/AdaCore/gnat_community_install_script
sh ./gnat_community_install_script/install_package.sh ./gnat-community-2018 /opt/gnat-community-2018
