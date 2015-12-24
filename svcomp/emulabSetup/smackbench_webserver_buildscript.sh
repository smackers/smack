#!/bin/bash

#Install htop
sudo apt-get update
sudo apt-get install htop -y
sudo apt-get install apache2 -y

#Change document root 
sudo sed -i 's,/var/www/html,/proj/SMACK/SMACKBenchResults/data,g' /etc/apache2/sites-available/000-default.conf
#Add directory configuration (inserts after documentroot directive)
sudo awk '/DocumentRoot/ {print;
print "        <Directory /proj/SMACK/SMACKBenchResults/data>";
print "            Options Indexes FollowSymLinks ExecCGI";
print "            AddHandler cgi-script .py";
print "            AllowOverride None";
print "            Require all granted";
print "            DirectoryIndex index.py";
print "            # This causes these files to be downloaded, vs displaying";
print "            # directly in browser";
print "            <FilesMatch '\''\.(bc|bpl|graphml)$'\''>";
print "                        Header set Content-Disposition attachment";
print "                        ForceType application/octet-stream";
print "            </FilesMatch>";
print "        </Directory>";
next}1' /etc/apache2/sites-available/000-default.conf > /tmp/tmp && sudo mv /tmp/tmp /etc/apache2/sites-available/000-default.conf
sudo a2enmod cgi
sudo a2enmod headers
sudo apache2ctl restart
sudo apache2ctl restart
