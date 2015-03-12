Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox"
  config.vm.box = "ubuntu/trusty64"
  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.provision "shell", inline: <<-SHELL
    cd /home/vagrant
    ./#{project_name}/bin/build.sh
    echo source smack.environment >> .bashrc
    echo cd #{project_name} >> .bashrc
  SHELL

end
