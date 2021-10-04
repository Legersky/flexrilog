FROM registry.gitlab.com/sagemath/sage/sagemath:9.3

COPY --chown=sage:sage . ${HOME}

RUN sudo apt-get update && sudo apt-get install make

RUN make install
