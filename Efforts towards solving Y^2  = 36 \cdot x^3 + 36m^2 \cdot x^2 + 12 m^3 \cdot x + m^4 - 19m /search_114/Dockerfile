FROM ubuntu:24.04

RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        build-essential \
        libgmp-dev \
        libgmp10 && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY search114_rational.c .
RUN gcc -O3 -o search114_rational search114_rational.c -lgmp

COPY run_rational.sh .
RUN chmod +x run_rational.sh

ENTRYPOINT ["/bin/bash", "run_rational.sh"]
