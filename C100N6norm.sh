#!/bin/bash

#SBATCH --time=240:00:00
#SBATCH --mem-per-cpu=16G
#SBATCH --cpus-per-task=1
#SBATCH --job-name="C100N6norm"

module load nixpkgs/16.09 gcc/8.3.0 gsl/2.6 r/4.0.0

Rscript C100N6norm.R
