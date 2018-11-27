Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox" do |vb|
    # vb.memory = 2048 # control VM memory (set it to 2GB)
    vb.customize ["modifyvm", :id, "--usb", "off"]
    vb.customize ["modifyvm", :id, "--usbehci", "off"]
  end
  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.define :ubuntu do |ubuntu_config|
    ubuntu_config.vm.box = "bento/ubuntu-16.04"
  end

  # This provision, 'fix-no-tty', gets rid of an error during build
  # which says "==> default: stdin: is not a tty"
  config.vm.provision "fix-no-tty", type: "shell" do |s|
    s.privileged = false
    s.inline = "sudo sed -i '/tty/!s/mesg n/tty -s \\&\\& mesg n/' /root/.profile"
  end

  # TODO ability to choose between the two?
  # config.vm.define :opensuse do |opensuse_config|
  #   opensuse_config.vm.box = "chef/opensuse-13.1"
  # end

  config.vm.provision "shell", binary: true, inline: <<-SHELL
    apt-get update
    apt-get install -y software-properties-common
    cd /home/vagrant
    ./#{project_name}/bin/build.sh
    echo source smack.environment >> .bashrc
    echo cd #{project_name} >> .bashrc
  SHELL

end
