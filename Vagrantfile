Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox"
  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.define :ubuntu do |ubuntu_config|
    ubuntu_config.vm.box = "ubuntu/trusty64"
  end

  # TODO ability to choose between the two?
  # config.vm.define :opensuse do |opensuse_config|
  #   opensuse_config.vm.box = "chef/opensuse-13.1"
  # end

  config.vm.provision "shell", inline: <<-SHELL
    cd /home/vagrant
    ./#{project_name}/bin/build.sh
    echo source smack.environment >> .bashrc
    echo cd #{project_name} >> .bashrc
  SHELL

end
