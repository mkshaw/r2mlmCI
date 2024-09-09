tictoc::tic()
# 1 Simulation Setup ------------------------------------------------------

# Load libraries
# modelling dependencies
library(r2mlm)
library(DescTools) # for confidence intervals
library(bootmlm) # for bootstrapping
library(magrittr) # for pipe
library(glue) # for printing coverage intervals

# data creation dependencies
library(rockchalk)
library(tidyverse)
library(lme4)
library(nlme)
library(lmerTest)
library(MASS)
library(truncnorm)
library(covsim) # non-normal errors

# Manipulated study conditions
C.cond <- 200
N.cond <- 25 # cluster size
norm.cond <- "nonnormal" # error normality

# name outfile
outfile <- glue("C{C.cond}N{N.cond}{norm.cond}")

# Fixed conditions
# data generation
#fixed component of intercept
# gamma00 <- 10
# 
# #fixed components of level-2 variables
# gamma01 <- -1.5
# gamma02 <- -1.5
# gamma03 <- -1.5
# 
# #fixed component of level-1 variables
# gamma10 <- 1.5
# gamma20 <- 1.5
# gamma30 <- 1.5
# 
# ##random effect (co)variances
# tau00 <- 3.0
# tau11 <- 1.0
# tau22 <- 1.0
# tau33 <- 1.0
# tau01 <- tau02 <- tau03 <- tau12 <- tau13 <- tau23 <- 0
# 
# Tau <- matrix(c(tau00, tau01, tau02, tau03,
#                 tau01, tau11, tau12, tau13,
#                 tau02, tau12, tau22, tau23,
#                 tau03, tau13, tau23, tau33), 4, 4)
# sigma2 <- 3.5

# Data generation -- near-zero R2s
# Fixed conditions
#fixed component of intercept
gamma00 <- 4

#fixed components of level-2 variables
gamma01 <- -1.25
gamma02 <- -1.25
gamma03 <- -1.25

#fixed component of level-1 variables
gamma10 <- 1.5
gamma20 <- 1.5
gamma30 <- 1.5

##random effect (co)variances
tau00 <- 7
tau11 <- 1
tau22 <- 1
tau33 <- 1
tau01 <- tau02 <- tau03 <- tau12 <- tau13 <- tau23 <- 0

Tau <- matrix(c(tau00, tau01, tau02, tau03,
                tau01, tau11, tau12, tau13,
                tau02, tau12, tau22, tau23,
                tau03, tau13, tau23, tau33), 4, 4)
sigma2 <- 12

# population R2s
##arguments:
#l1slope = fixed component of l1 predictor slopes
#l2slope = fixed component of l2 predictor slopes
#randslopevar = random slope variance for each l1 predictor
#randintvar = random intercept variance
#sig2 = level-1 error variance

returnpopr2 <- function(l1slope, l2slope, randslopevar, randintvar, sig2){
  #fixed component of intercept (arbitrary)
  gamma00 <- gamma00
  #fixed component of xs
  gamma10 <- gamma20 <- gamma30 <- l1slope
  #fixed component of ws
  gamma01 <- gamma02 <- gamma03 <- l2slope
  
  ##random effect (co)variances
  tau00 <- randintvar
  tau11 <- tau22 <- tau33 <- randslopevar
  tau01 <- 0
  tau02 <- 0
  tau03 <- 0
  tau12 <- 0
  tau13 <- 0
  tau23 <- 0
  Tau <- matrix(c(tau00,tau01,tau02,tau03,
                  tau01,tau11,tau12,tau13,
                  tau02,tau12,tau22,tau23,
                  tau03,tau13,tau23,tau33),4,4)
  sigma2 <- sig2
  
  ##predictor variances
  var_x1 <- 1
  var_x2 <- 1
  var_x3 <- 1
  cov_x12 <- 0
  cov_x13 <- 0
  cov_x23 <- 0
  var_w1 <- 1
  var_w2 <- 1
  var_w3 <- 1
  cov_w12 <- 0
  cov_w13 <- 0
  cov_w23 <- 0
  
  ###compute population R2
  gamma_w <- matrix(c(gamma10,gamma20,gamma30),ncol=1)
  gamma_b <- matrix(c(gamma01,gamma02,gamma03),ncol=1)
  phi_w <- matrix(c(var_x1,cov_x12,cov_x13,
                    cov_x12,var_x2,cov_x23,
                    cov_x13,cov_x23,var_x3),3,3)
  phi_b <- matrix(c(var_w1,cov_w12,cov_w13,
                    cov_w12,var_w2,cov_w23,
                    cov_w13,cov_w23,var_w3),3,3)
  ##assuming all level-1 predictors have random slopes
  Sig_w <- phi_w 
  
  f1 <- t(gamma_w) %*% phi_w %*% gamma_w
  f2 <- t(gamma_b) %*% phi_b %*% gamma_b
  v <- sum(diag(Tau[2:4,2:4]%*%Sig_w))
  m <- Tau[1,1]
  sig <- sigma2
  
  withinvar <- f1 + v + sig
  betweenvar <- f2 + m
  totalvar <- withinvar + betweenvar
  
  R2_f1_t <- f1/(totalvar)
  R2_f2_t <- f2/(totalvar)
  R2_v_t <- v/(totalvar)
  R2_m_t <- m/(totalvar)
  
  R2_f1_w <- f1/(withinvar)
  R2_f2_b <- f2/(betweenvar)
  R2_v_w <- v/(withinvar)
  R2_m_b <- m/(betweenvar) 
  
  ##create table to output R-squared values
  contributions_stacked <- matrix(c(R2_f1_t, R2_f2_t, R2_v_t, R2_m_t, 1-sum(R2_f1_t, R2_f2_t, R2_v_t, R2_m_t),
                                    R2_f1_w, 0, R2_v_w, 0, 1-sum(R2_f1_w,R2_v_w),
                                    0, R2_f2_b, 0, R2_m_b, 0), 5, 3)
  colnames(contributions_stacked) <- c("total", "within", "between")
  rownames(contributions_stacked) <- c("fixed slopes (within)",
                                       "fixed slopes (between)",
                                       "slope variation (within)",
                                       "intercept variation (between)",
                                       "residual (within)")
  
  return(contributions_stacked)
}
popr2s <- returnpopr2(l1slope = gamma10, l2slope = gamma01, randslopevar = tau11, randintvar = tau00, sig2 = sigma2)

# effect sizes
f1 <- popr2s[1, 1]
f2 <- popr2s[2, 1]
v  <- popr2s[3, 1]
m  <- popr2s[4, 1]

# coverage iterations
nrep <- 200

# bootstrap iterations
brep <- 500

# model
form <- formula(satisfaction ~ 1 + x1 + x2 + x3 + z1 + z2 + z3 + (1 + x1 + x2 + x3|schoolID))

# Set random number seed
set.seed(1996)

# Functions
# create data
#satisfaction <- gamma00 + gamma01*z1 + gamma02*z2 + gamma03*z3 + gamma10*x1 + gamma20*x2 + gamma30*x3 + u0j + u1j*x1 + u2j*x2 + u3j*x3 + eij
create_df <- function(C, N, norm) {
  
  #fixed component of intercept
  gamma00 <- gamma00
  
  #fixed component of level-2 variables
  gamma01 <- gamma01
  gamma02 <- gamma02
  gamma03 <- gamma03
  
  #fixed component of level-1 variables
  gamma10 <- gamma10
  gamma20 <- gamma20
  gamma30 <- gamma30
  
  ##random effect (co)variances
  tau00 <- tau00
  tau11 <- tau11
  tau22 <- tau22
  tau33 <- tau33
  # covariances are defined above in fixed conditions section
  
  Tau <- matrix(c(tau00, tau01, tau02, tau03,
                  tau01, tau11, tau12, tau13,
                  tau02, tau12, tau22, tau23,
                  tau03, tau13, tau23, tau33), 4, 4)
  sigma2 <- sigma2
  
  #set sample size
  clusters <- C
  clustersize <- N
  
  ##make dataset
  teachsat <- as.data.frame(matrix(NA, clusters*clustersize, 14))
  colnames(teachsat) <- c("schoolID", "teacherID", "satisfaction", "x1", "x2", "x3", "z1", "z2", "z3", "u0j", "u1j", "u2j", "u3j", "eij")
  
  teachsat[,"schoolID"] <- rep(seq(clusters), each = clustersize)
  teachsat[,"teacherID"] <- rep(seq(clustersize), clusters)
  
  #generate predictors
  teachsat[,"x1"] <- (rnorm(clusters*clustersize, mean=0, sd=sqrt(clustersize/(clustersize - 1))))
  teachsat[,"x2"] <- (rnorm(clusters*clustersize, mean=0, sd=sqrt(clustersize/(clustersize - 1))))
  teachsat[,"x3"] <- (rnorm(clusters*clustersize, mean=0, sd=sqrt(clustersize/(clustersize - 1))))
  
  teachsat[,"z1"] <- rep(rnorm(clusters, mean = 0, sd = 1), each=clustersize) #rnorm(clusters, mean = 0, sd = 1) generates 300 numbers from normal distribution, rep() repeats each number 30 times
  teachsat[,"z2"] <- rep(rnorm(clusters, mean = 0, sd = 1), each=clustersize)
  teachsat[,"z3"] <- rep(rnorm(clusters, mean = 0, sd = 1), each=clustersize)
  
  #generate errors by normality condition
  if (norm == "normal") {
    teachsat[,"eij"] <- rnorm(clusters*clustersize, 0, sqrt(sigma2))
    randomeffects <- mvrnorm(clusters, c(0, 0, 0, 0), Tau)
    teachsat[,"u0j"] <- rep(randomeffects[,1], each=clustersize)
    teachsat[,"u1j"] <- rep(randomeffects[,2], each=clustersize) 
    teachsat[,"u2j"] <- rep(randomeffects[,3], each=clustersize) 
    teachsat[,"u3j"] <- rep(randomeffects[,4], each=clustersize)
  } else if (norm == "nonnormal") {
    sk <- 2
    kurt <- 7
    obs <- clusters*clustersize
    teachsat[,"eij"] <- rIG(obs, as.matrix(sigma2), sk, kurt, 1)[[1]]
    teachsat[,"u0j"] <- rep(rIG(clusters, as.matrix(tau00), sk, kurt, 1)[[1]], each = clustersize)
    teachsat[,"u1j"] <- rep(rIG(clusters, as.matrix(tau11), sk, kurt, 1)[[1]], each = clustersize)
    teachsat[,"u2j"] <- rep(rIG(clusters, as.matrix(tau22), sk, kurt, 1)[[1]], each = clustersize)
    teachsat[,"u3j"] <- rep(rIG(clusters, as.matrix(tau33), sk, kurt, 1)[[1]], each = clustersize)
  } else {
    print("something went wrong with the error normality")
  }
  
  #group-mean-center level-1 vars
  teachsat <- gmc(teachsat, c("x1", "x2", "x3"), "schoolID")
  teachsat$x1 <- teachsat$x1_dev
  teachsat$x2 <- teachsat$x2_dev
  teachsat$x3 <- teachsat$x3_dev
  
  #generate outcome
  for(i in seq(clusters*clustersize)){
    teachsat[i,"satisfaction"] <- gamma00 + gamma01*teachsat[i,"z1"] + gamma02*teachsat[i,"z2"] + gamma03*teachsat[i, "z3"] +
      gamma10*teachsat[i,"x1"] + gamma20*teachsat[i,"x2"] + gamma30*teachsat[i,"x3"] + teachsat[i,"u0j"] + 
      teachsat[i,"u1j"]*teachsat[i,"x1"] + teachsat[i,"u2j"]*teachsat[i,"x2"] + teachsat[i,"u3j"]*teachsat[i,"x3"] +
      teachsat[i,"eij"]
  }
  
  #remove unnecessary vars (dev, mn, errors)
  teachsat<-teachsat[,-c(10:20)]
  df <- teachsat
  return(df)
  
}

# get R2s
r2s <- function(.) {
  # r2mlm(., bargraph = F)$R2s %>% as.double()
  temp <- as.double(r2mlm(., bargraph = F)$R2s)[c(1:4)] %>% 
    suppressWarnings()
  temp <- c(temp, .@beta[1:3]) #beta[1:3] just takes the first 3 fixed effects, because we don't want all of them, our focus is R2s
  names(temp) <- c("f1t", "f2t", "vt", "mt", "gamma00", "gamma10", "gamma01")
  c(temp)
}

# 2 Run Simulation --------------------------------------------------------

results <- matrix(numeric(), nrow = 0, ncol = 10)

for (C in C.cond) {
  for (N in N.cond) {
    for (norm in norm.cond) {
      
      # nonconvergence tally
      nonconvergence = 0
      
      # confidence interval holder
      confints_par_norm <- matrix(numeric(), nrow = 0, ncol = 2)
      confints_res_norm <- matrix(numeric(), nrow = 0, ncol = 2)
      confints_par_basic <- matrix(numeric(), nrow = 0, ncol = 2)
      confints_res_basic <- matrix(numeric(), nrow = 0, ncol = 2)
      confints_par_perc <- matrix(numeric(), nrow = 0, ncol = 2)
      confints_res_perc <- matrix(numeric(), nrow = 0, ncol = 2)
      
      for (r in 1:nrep) {
        
        # create dataset
        dat <- create_df(C, N, norm)
        
        # bootstrap datasets
        mod <- lmer(form, dat, control = lmerControl(optimizer = "bobyqa"))
        
        if (length(warnings()) > 0) {
          nonconvergence = nonconvergence + 1
          print("Nonconvergence added to tally")
          assign("last.warning", NULL, envir = baseenv())
        } else {
          boopar <- bootstrap_mer(x = mod,
                                  FUN = r2s,
                                  nsim = brep,
                                  type = c("parametric"))
          boores <- bootstrap_mer(x = mod,
                                  FUN = r2s,
                                  nsim = brep,
                                  type = c("residual"))
          
          # get confidence intervals and store them
          confints_par_norm <- rbind(confints_par_norm, confint(boopar, type = "norm"))
          confints_res_norm <- rbind(confints_res_norm, confint(boores, type = "norm"))
          
          confints_par_basic <- rbind(confints_par_basic, confint(boopar, type = "basic"))
          confints_res_basic <- rbind(confints_res_basic, confint(boores, type = "basic"))
          
          confints_par_perc <- rbind(confints_par_perc, confint(boopar, type = "perc"))
          confints_res_perc <- rbind(confints_res_perc, confint(boores, type = "perc"))
          
          # remove warnings about confints
          assign("last.warning", NULL, envir = baseenv())
        }
        
        # print statement for progress updates
        print(glue("Completed iteration number {r} out of {nrep}"))
        
      }
      
      # calculate coverage across confidence intervals and store ----
      # f1 norm
      converged_rep = nrep - nonconvergence
      f1pn <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_par_norm[i, 1] && f1 <= confints_par_norm[i, 2]) {
          f1pn <- f1pn + 1
        }
      }
      f1pn <- f1pn/converged_rep
      
      f1rn <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_res_norm[i, 1] && f1 <= confints_res_norm[i, 2]) {
          f1rn <- f1rn + 1
        }
      }
      f1rn <- f1rn/converged_rep
      
      # f1 basic
      f1pb <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_par_basic[i, 1] && f1 <= confints_par_basic[i, 2]) {
          f1pb <- f1pb + 1
        }
      }
      f1pb <- f1pb/converged_rep
      
      f1rb <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_res_basic[i, 1] && f1 <= confints_res_basic[i, 2]) {
          f1rb <- f1rb + 1
        }
      }
      f1rb <- f1rb/converged_rep
      
      # f1 perc
      f1pp <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_par_perc[i, 1] && f1 <= confints_par_perc[i, 2]) {
          f1pp <- f1pp + 1
        }
      }
      f1pp <- f1pp/converged_rep
      
      f1rp <- 0
      for (i in seq(from = 1, to = converged_rep*7, by = 7)) {
        if (f1 >= confints_res_perc[i, 1] && f1 <= confints_res_perc[i, 2]) {
          f1rp <- f1rp + 1
        }
      }
      f1rp <- f1rp/converged_rep
      
      # f2 norm
      f2pn <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_par_norm[i, 1] && f2 <= confints_par_norm[i, 2]) {
          f2pn <- f2pn + 1
        }
      }
      f2pn <- f2pn/converged_rep
      
      f2rn <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_res_norm[i, 1] && f2 <= confints_res_norm[i, 2]) {
          f2rn <- f2rn + 1
        }
      }
      f2rn <- f2rn/converged_rep
      
      # f2 basic
      f2pb <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_par_basic[i, 1] && f2 <= confints_par_basic[i, 2]) {
          f2pb <- f2pb + 1
        }
      }
      f2pb <- f2pb/converged_rep
      
      f2rb <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_res_basic[i, 1] && f2 <= confints_res_basic[i, 2]) {
          f2rb <- f2rb + 1
        }
      }
      f2rb <- f2rb/converged_rep
      
      # f2 perc
      f2pp <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_par_perc[i, 1] && f2 <= confints_par_perc[i, 2]) {
          f2pp <- f2pp + 1
        }
      }
      f2pp <- f2pp/converged_rep
      
      f2rp <- 0
      for (i in seq(from = 2, to = converged_rep*7, by = 7)) {
        if (f2 >= confints_res_perc[i, 1] && f2 <= confints_res_perc[i, 2]) {
          f2rp <- f2rp + 1
        }
      }
      f2rp <- f2rp/converged_rep
      
      # v norm
      vpn <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_par_norm[i, 1] && v <= confints_par_norm[i, 2]) {
          vpn <- vpn + 1
        }
      }
      vpn <- vpn/converged_rep
      
      vrn <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_res_norm[i, 1] && v <= confints_res_norm[i, 2]) {
          vrn <- vrn + 1
        }
      }
      vrn <- vrn/converged_rep
      
      # v basic
      vpb <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_par_basic[i, 1] && v <= confints_par_basic[i, 2]) {
          vpb <- vpb + 1
        }
      }
      vpb <- vpb/converged_rep
      
      vrb <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_res_basic[i, 1] && v <= confints_res_basic[i, 2]) {
          vrb <- vrb + 1
        }
      }
      vrb <- vrb/converged_rep
      
      # v perc
      vpp <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_par_perc[i, 1] && v <= confints_par_perc[i, 2]) {
          vpp <- vpp + 1
        }
      }
      vpp <- vpp/converged_rep
      
      vrp <- 0
      for (i in seq(from = 3, to = converged_rep*7, by = 7)) {
        if (v >= confints_res_perc[i, 1] && v <= confints_res_perc[i, 2]) {
          vrp <- vrp + 1
        }
      }
      vrp <- vrp/converged_rep
      
      # m norm
      mpn <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_par_norm[i, 1] && m <= confints_par_norm[i, 2]) {
          mpn <- mpn + 1
        }
      }
      mpn <- mpn/converged_rep
      
      mrn <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_res_norm[i, 1] && m <= confints_res_norm[i, 2]) {
          mrn <- mrn + 1
        }
      }
      mrn <- mrn/converged_rep
      
      # m basic
      mpb <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_par_basic[i, 1] && m <= confints_par_basic[i, 2]) {
          mpb <- mpb + 1
        }
      }
      mpb <- mpb/converged_rep
      
      mrb <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_res_basic[i, 1] && m <= confints_res_basic[i, 2]) {
          mrb <- mrb + 1
        }
      }
      mrb <- mrb/converged_rep
      
      # m percent
      mpp <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_par_perc[i, 1] && m <= confints_par_perc[i, 2]) {
          mpp <- mpp + 1
        }
      }
      mpp <- mpp/converged_rep
      
      mrp <- 0
      for (i in seq(from = 4, to = converged_rep*7, by = 7)) {
        if (m >= confints_res_perc[i, 1] && m <= confints_res_perc[i, 2]) {
          mrp <- mrp + 1
        }
      }
      mrp <- mrp/converged_rep
      
      # format outfiles ----
      
      outpar_norm <- c(C, N, norm, "parametric", "norm", f1pn, f2pn, vpn, mpn, converged_rep)
      outres_norm <- c(C, N, norm, "residual", "norm", f1rn, f2rn, vrn, mrn, converged_rep)
      
      outpar_perc <- c(C, N, norm, "parametric", "perc", f1pp, f2pp, vpp, mpp, converged_rep)
      outres_perc <- c(C, N, norm, "residual", "perc", f1rp, f2rp, vrp, mrp, converged_rep)
      
      outpar_basic <- c(C, N, norm, "parametric", "basic", f1pb, f2pb, vpb, mpb, converged_rep)
      outres_basic <- c(C, N, norm, "residual", "basic", f1rb, f2rb, vrb, mrb, converged_rep)
      
      # bind to results
      results <- rbind(results, outpar_norm, outres_norm, outpar_perc, outres_perc, outpar_basic, outres_basic)
      print(results)
    }
  }
}

# Clean up results
colnames(results) <- c("C", "N", "norm", "boottype", "CI", "f1cov", "f2cov", "vcov", "mcov", "converged_reps")

results <- as.data.frame(results)
results <- results %>% 
  mutate(C = as.numeric(paste(C)),
         N = as.numeric(paste(N)),
         f1cov = as.numeric(paste(f1cov)),
         f2cov = as.numeric(paste(f2cov)),
         vcov = as.numeric(paste(vcov)),
         mcov = as.numeric(paste(mcov)),
         averagecov = (f1cov + f2cov + vcov + mcov)/4,
         nonconverge_prop = 1 - (as.numeric(paste(converged_reps))/nrep)) # paste required to get numbers from converged_reps as opposed to factor level (which returns 1)
write.csv(results, glue("results/{outfile}.csv"))

tictoc::toc()
