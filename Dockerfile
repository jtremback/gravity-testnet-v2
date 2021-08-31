FROM fedora:34
ENV GOPATH=/go
ENV PATH=$PATH:/go/bin
RUN dnf install -y git make gcc gcc-c++ which iproute iputils procps-ng vim-minimal tmux net-tools htop tar jq npm openssl-devel perl rust cargo golang

# Copy in the repo under test
ADD ./cosmos-gravity-bridge /cosmos-gravity-bridge

# Build the Go module
RUN pushd /cosmos-gravity-bridge/module/ && PATH=$PATH:/usr/local/go/bin GOPROXY=https://proxy.golang.org make && PATH=$PATH:/usr/local/go/bin make install

# This step just downloads and caches the deps and gets past a long "Updating crates.io index" step
COPY ./rust/Cargo.toml /rust/Cargo.toml
COPY ./fake-main.rs /rust/src/main.rs
RUN pushd /rust/ && cargo fetch

# Actually build the rust code
ADD ./rust/ /rust
RUN pushd /rust/ && cargo build

# Copy in the shell scripts that run the testnet
ADD ./testnet-scripts /testnet-scripts