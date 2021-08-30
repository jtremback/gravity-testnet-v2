FROM fedora:34
ENV GOPATH=/go
ENV PATH=$PATH:/go/bin
RUN dnf install -y git make gcc gcc-c++ which iproute iputils procps-ng vim-minimal tmux net-tools htop tar jq npm openssl-devel perl rust cargo golang

ADD ./cosmos-gravity-bridge /gravity

RUN pushd /gravity/module/ && PATH=$PATH:/usr/local/go/bin GOPROXY=https://proxy.golang.org make && PATH=$PATH:/usr/local/go/bin make install

ADD ./testnet-scripts /testnet-scripts