docker run -it --rm -v "${PWD}:/coq_project" -w /coq_project coqorg/coq coqtop


docker run --name coq_runner -v "${PWD}:/coq_project" -w /coq_project coqorg/coq:latest coqc main.v

docker run -it --name coq_runner -v "${PWD}:/coq_project" -w /coq_project coqorg/coq:latest coqtop main.v


docker exec -it coq_runner /bin/bash

