FROM easycryptpa/ec-build-box:latest

RUN \
	opam pin --dev-repo add -n easycrypt https://github.com/EasyCrypt/easycrypt.git#${SOURCE_BRANCH:-1.0} && \
	opam install -v easycrypt.dev && \
	rm -rf .opam/packages.dev/*
