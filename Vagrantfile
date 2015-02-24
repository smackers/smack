Vagrant.configure(2) do |config|

  project_name = File.dirname(__FILE__).split("/").last

  config.vm.provider "virtualbox"
  config.vm.box = "ubuntu/trusty64"
  config.vm.synced_folder ".", "/home/vagrant/#{project_name}"

  config.vm.provision "shell", inline: <<-SHELL

    add-apt-repository "deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.5 main"
    wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key | sudo apt-key add -
    apt-get update
    apt-get install -y clang-3.5 clang-3.5-doc libclang-common-3.5-dev libclang-3.5-dev libclang1-3.5 libclang1-3.5-dbg libllvm3.5 libllvm3.5-dbg lldb-3.5 llvm-3.5 llvm-3.5-dev llvm-3.5-doc llvm-3.5-runtime lldb-3.5-dev
    update-alternatives --install /usr/bin/clang clang /usr/bin/clang-3.5 20
    update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-3.5 20
    update-alternatives --install /usr/bin/llvm-config llvm-config /usr/bin/llvm-config-3.5 20
    update-alternatives --install /usr/bin/llvm-link llvm-link /usr/bin/llvm-link-3.5 20
    apt-get install -y libz-dev libedit-dev mono-complete git mercurial cmake python-yaml unzip

    cd /home/vagrant

    # Z3
    wget "http://download-codeplex.sec.s-msft.com/Download/SourceControlFileDownload.ashx?ProjectName=z3&changeSetId=cee7dd39444c9060186df79c2a2c7f8845de415b"
    unzip SourceControlFileDownload* -d z3
    rm -f SourceControlFileDownload*
    cd z3
    python scripts/mk_make.py
    cd build
    make
    make install
    cd ../..

    # Boogie
    hg clone -r 15f47e2eec5d https://hg.codeplex.com/boogie
    cd boogie/Source
    mozroots --import --sync
    wget https://nuget.org/nuget.exe
    mono ./nuget.exe restore Boogie.sln
    xbuild Boogie.sln /p:Configuration=Release
    cd ..
    ln -s /home/vagrant/z3/build/z3 Binaries/z3.exe
    cd ..

    # Corral
    git clone https://git01.codeplex.com/corral
    cd corral
    git checkout 8fee716e3665
    cp ../boogie/Binaries/*.{dll,exe} references
    xbuild cba.sln /p:Configuration=Release
    ln -s /home/vagrant/z3/build/z3 bin/Release/z3.exe
    cd ..

    # SMACK
    cd #{project_name}
    rm -rf build
    mkdir build
    cd build
    cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DLLVM_CONFIG=/usr/bin -DCMAKE_BUILD_TYPE=Release ..
    make install
    cd ../..

    # Shell environment
    echo export BOOGIE=\\"mono $(pwd)/boogie/Binaries/Boogie.exe\\" >> .bashrc
    echo export CORRAL=\\"mono $(pwd)/corral/bin/Release/corral.exe\\" >> .bashrc
    echo cd #{project_name} >> .bashrc

  SHELL

end
