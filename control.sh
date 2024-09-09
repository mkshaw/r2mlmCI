#!/bin/bash

#SBATCH --time=24:00:00
#SBATCH --mem-per-cpu=16G
#SBATCH --cpus-per-task=18
#SBATCH --job-name="control_test"

module load nixpkgs/16.09 gcc/8.3.0 gsl/2.6 r/4.0.0

Rscript control.R
