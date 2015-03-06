# -*- mode: ruby -*-
# vi: set ft=ruby :

# All Vagrant configuration is done below. The "2" in Vagrant.configure
# configures the configuration version (we support older styles for
# backwards compatibility). Please don't change it unless you know what
# you're doing.
Vagrant.configure(2) do |config|
  config.vm.define "ubuntu" do |ubuntu|

    ubuntu.vm.box = "ubuntu/trusty64"

    # VM configurations
    # View the documentation for the VirtualBox provider for more
    # information on available options.
    # https://docs.vagrantup.com/v2/virtualbox/configuration.html

    ubuntu.vm.provider "virtualbox" do |vb|
      # Customize the amount of memory on the VM:
      vb.memory = "512"

      # Customize the amount of CPUs on the VM:
      #vm.cpus = 1
    end

    # Provision the VM
    ubuntu.vm.provision "shell" do |s|
      # replace Windows line endings with Unix line endings
      s.binary = true

      s.inline = "sudo apt-get update;
                  sudo bash /vagrant/bin/build-ubuntu-14.04.1-cmake.sh;"
    end
  end

  config.vm.define "opensuse" do |opensuse|

    opensuse.vm.box = "chef/opensuse-13.1"

    # VM configurations
    opensuse.vm.provider "virtualbox" do |vb|
      # Customize the amount of memory on the VM:
      vb.memory = "512"

      # Customize the amount of CPUs on the VM:
      #vm.cpus = 1
    end

    # Provision the VM
    opensuse.vm.provision "shell" do |s|
      # replace Windows line endings with Unix line endings
      s.binary = true

      s.inline = "sudo zypper refresh;
                  sudo zypper --non-interactive update;
                  sudo bash /vagrant/bin/build-opensuse-cmake.sh;"
    end
  end

end
