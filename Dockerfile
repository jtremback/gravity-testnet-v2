FROM fedora:34
ENV GOPATH=/go
ENV PATH=$PATH:/go/bin
RUN dnf install -y git make gcc gcc-c++ which iproute iputils procps-ng vim-minimal tmux net-tools htop tar jq npm openssl-devel perl rust cargo golang

ADD ./cosmos-gravity-bridge /cosmos-gravity-bridge
RUN pushd /cosmos-gravity-bridge/module/ && PATH=$PATH:/usr/local/go/bin GOPROXY=https://proxy.golang.org make && PATH=$PATH:/usr/local/go/bin make install

COPY ./rust/Cargo.toml ./rust/Cargo.toml
COPY ./fake-main.rs ./rust/src/main.rs
RUN pushd /rust/ && cargo build && rm -rf /rust/

ADD ./rust/ /rust
RUN pushd /rust/ && cargo build

ADD ./testnet-scripts /testnet-scripts