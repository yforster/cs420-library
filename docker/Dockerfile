FROM ubuntu:22.04

RUN apt-get update && \
    apt-get install --yes \
        wine \
        7zip \
        wget \
        && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/*

# Install Coq
ARG COQ_URL=https://github.com/coq/platform/releases/download/2022.04.0/Coq-Platform-release-2022.04.0-version_8.15_2022.04-windows-x86_64_signed.exe#/dl.7z
RUN \
    mkdir /opt/coq && \
    cd /opt/coq && \
    wget $COQ_URL -O coq.7z && \
    7zz x coq.7z && \
    rm coq.7z

# Install PowerShell
ARG PWSH_URL=https://github.com/PowerShell/PowerShell/releases/download/v7.2.6/powershell-lts_7.2.6-1.deb_amd64.deb
RUN wget $PWSH_URL -O /tmp/powershell.deb && \
    dpkg -i /tmp/powershell.deb && \
    rm -f /tmp/powershell.deb

# Make sure wine is not complaining at us
ENV WINEDEBUG=-all

# Add a default user
RUN useradd -m builder
USER builder
WORKDIR /home/builder
