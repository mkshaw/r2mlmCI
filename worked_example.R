# worked example

# 0 Load data and dependencies --------------------------------------------

library(r2mlm)
library(lme4)

r2mlm_ci <- function(model, nsim, boottype, confinttype, level = 0.95, progress = T) {
  
  # function to calculate r2s
  r2s <- function(.) {
    r2mlm(., bargraph = F)$R2s[c(1:8, 10, 13, 16, 18)]
  }
  
  boo <- bootmlm::bootstrap_mer(x = model,
                                FUN = r2s,
                                nsim = nsim,
                                type = boottype,
                                .progress = progress)
  
  tryCatch(
    expr = {
      confints <- confint(boo,
                          type = confinttype,
                          level = level)
      rownames(confints) <- c("f1_total", "f2_total", "v_total", "m_total", "f_total", "fv_total", "fvm_total", "f1_within", "v_within", "fv_within", "f2_between", "m_between")
      return(confints)
    },
    error = function(e) {
      # proper dimensions for t if not centered
      boo$t0 <- boo$t0[1:5] # only 5 R2s
      boo$t <- boo$t[1:nsim, 1:5] # matrix of 5 R2 values for number of simulations
      confints <- confint(boo,
                          type = confinttype,
                          level = level)
      rownames(confints) <- c("f_total", "v_total", "m_total", "fv_total", "fvm_total")
      return(confints)
    }
  )
  
  
}

# 1 Model -----------------------------------------------------------------

model <- lmer(satisfaction ~ 1 + control_c + salary_c + s_t_ratio +
                (1 + control_c|schoolID),
              data = teachsat,
              REML = F)
summary(model)
r2mlm(model)

r2mlm_ci(model = model,
         nsim = 500,
         boottype = "residual",
         confinttype = "perc",
         level = 0.95,
         progress = T)
