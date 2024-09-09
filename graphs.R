# 0 Load Data -------------------------------------------------------------

library(ggplot2)
library(dplyr)
library(patchwork)
library(glue)

# filenames of results
result_filenames <- list.files("results/")

# start df
results <- read.csv(glue("results/{result_filenames[1]}"))

# rest of results
for (result in result_filenames[-1]) {
  results <- rbind(results, read.csv(glue("results/{result}")))
}

results <- results %>% 
  mutate(
         N = as.factor(N)) %>%
  rename(Coverage = averagecov) %>% 
  rowwise() %>% 
  mutate(mincov = min(f1cov, f2cov, vcov, mcov),
         maxcov = max(f1cov, f2cov, vcov, mcov))

head(results)

# 1 Table -----------------------------------------------------------------

knitr::kable(results)

# 2 Graph -----------------------------------------------------------------

pd <- position_dodge(width = 0.4)

graph <- function(data, coverage, ci_type) {
  
  # all should have titles, but only percentile should have y-axis label
  if(ci_type == "perc") {
    data %>% 
      filter(CI == ci_type) %>% 
      ggplot(mapping = aes(x = C, y = .data[[coverage]], colour = factor(N))) +
      geom_point() +
      geom_line() +
      facet_grid(norm ~ boottype) +
      ylim(0.65, 1) +
      theme_bw() +
      theme(legend.position = "none",
            plot.title = element_text(hjust = 0.5)) +
      geom_hline(yintercept = 0.95, linetype = "dotted") +
      scale_x_continuous(breaks = c(30, 100, 200), labels = c(30, 100, 200), limits = c(10, 220)) +
      labs(title = "Percentile")
  } else if(ci_type == "norm") {
    data %>% 
      filter(CI == ci_type) %>% 
      ggplot(mapping = aes(x = C, y = .data[[coverage]], colour = factor(N))) +
      geom_point() +
      geom_line() +
      facet_grid(norm ~ boottype) +
      ylim(0.65, 1) +
      theme_bw() +
      theme(legend.position = "none",
            axis.title.y = element_blank(),
            plot.title = element_text(hjust = 0.5)) +
      geom_hline(yintercept = 0.95, linetype = "dotted") +
      scale_x_continuous(breaks = c(30, 100, 200), labels = c(30, 100, 200), limits = c(10, 220)) +
      labs(title = "Normal")
  } else if(ci_type == "basic") {
    data %>% 
      filter(CI == ci_type) %>% 
      ggplot(mapping = aes(x = C, y = .data[[coverage]], colour = factor(N))) +
      geom_point() +
      geom_line() +
      facet_grid(norm ~ boottype) +
      ylim(0.65, 1) +
      theme_bw() +
      theme(legend.position = "none",
            axis.title.y = element_blank(),
            plot.title = element_text(hjust = 0.5)) +
      geom_hline(yintercept = 0.95, linetype = "dotted") +
      scale_x_continuous(breaks = c(30, 100, 200), labels = c(30, 100, 200), limits = c(10, 220)) +
      labs(title = "Basic")
  }
  
}

graph_legend <- function(data, coverage, ci_type) {
  data %>% 
    filter(CI == ci_type) %>% 
    ggplot(mapping = aes(x = C, y = .data[[coverage]], colour = factor(N))) +
    geom_point() +
    geom_line() +
    facet_grid(norm ~ boottype) +
    ylim(0.65, 1) +
    theme_bw() +
    theme(axis.title.y = element_blank(),
          plot.title = element_text(hjust = 0.5)) +
    geom_hline(yintercept = 0.95, linetype = "dotted") +
    scale_x_continuous(breaks = c(30, 100, 200), labels = c(30, 100, 200), limits = c(10, 220)) +
    scale_color_manual(
      name = "N",
      values = c("6" = "#F8766D", "25" = "#00BA38", "70" = "#619CFF")
    ) +
    labs(title = "Normal")
}

# 2.1 f1 ------------------------------------------------------------------

percf1 <- graph(results, "f1cov", "perc"); percf1
basicf1 <- graph(results, "f1cov", "basic"); basicf1
normf1 <- graph_legend(results, "f1cov", "norm"); normf1
  
# 2.2 f2 ------------------------------------------------------------------

percf2 <- graph(results, "f2cov", "perc"); percf2
basicf2 <- graph(results, "f2cov", "basic"); basicf2
normf2 <- graph_legend(results, "f2cov", "norm"); normf2

# 2.3 v -------------------------------------------------------------------

percv <- graph(results, "vcov", "perc"); percv
basicv <- graph(results, "vcov", "basic"); basicv
normv <- graph_legend(results, "vcov", "norm"); normv

# 2.4 m -------------------------------------------------------------------

percm <- graph(results, "mcov", "perc"); percm
basicm <- graph(results, "mcov", "basic"); basicm
normm <- graph_legend(results, "mcov", "norm"); normm


# 3 Save Graphs -----------------------------------------------------------

# Create patchworks by R2
f1 <- percf1 + basicf1 + normf1; f1
ggsave("graphs/f1.png", plot = f1,
       width = 20,
       height = 12,
       units = "in")

f2 <- percf2 + basicf2 + normf2
ggsave("graphs/f2.png", plot = f2,
       width = 20,
       height = 12,
       units = "in")

v <- percv + basicv + normv
ggsave("graphs/v.png", plot = v,
       width = 20,
       height = 12,
       units = "in")

m <- percm + basicm + normm
ggsave("graphs/m.png", plot = m,
       width = 20,
       height = 12,
       units = "in")


# 4 Normal vs Basic vs Percentile CIs -------------------------------------

results %>% 
  group_by(CI) %>% # group by confidence interval
  mutate(f1mean = mean(f1cov), # calculate mean coverages for CIs
         f2mean = mean(f2cov),
         mmean = mean(mcov),
         vmean = mean(vcov)) %>% 
  filter(C == 100, N == 25, norm == "normal", boottype == "parametric") %>% 
  select(c(CI, f1mean, f2mean, mmean, vmean)) %>% 
  rowwise() %>% 
  summarize(CI,
            mean = mean(c_across(f1mean:vmean)))


# 5 Residual vs Parametric Bootstrapping ----------------------------------

results %>% 
  filter(norm == "normal") %>% 
  group_by(boottype) %>% # group by confidence interval
  mutate(f1mean = mean(f1cov), # calculate mean coverages for CIs
         f2mean = mean(f2cov),
         mmean = mean(mcov),
         vmean = mean(vcov)) %>% 
  filter(C == 100, N == 25) %>% 
  select(c(boottype, f1mean, f2mean, mmean, vmean)) %>% 
  rowwise() %>% 
  summarize(boottype,
            mean = mean(c_across(f1mean:vmean)))


results %>% 
  filter(norm == "nonnormal") %>% 
  group_by(boottype) %>% # group by confidence interval
  mutate(f1mean = mean(f1cov), # calculate mean coverages for CIs
         f2mean = mean(f2cov),
         mmean = mean(mcov),
         vmean = mean(vcov)) %>% 
  filter(C == 100, N == 25) %>% 
  select(c(boottype, f1mean, f2mean, mmean, vmean)) %>% 
  rowwise() %>% 
  summarize(boottype,
            mean = mean(c_across(f1mean:vmean)))


# 4 Export Results as One File --------------------------------------------

write.csv(results, file = "results.csv")

# 9000 Long-form graphs ---------------------------------------------------

basic <- results %>% 
  filter(CI == "basic") %>% # basic
  ggplot(mapping = aes(x = C, y = Coverage, colour = N)) +
  geom_point() +
  geom_errorbar(aes(ymin = mincov, ymax = maxcov, colour = N, alpha = .9)) +
  scale_alpha(guide = "none") +
  geom_line() +
  facet_grid(norm ~ boottype) +
  ylim(0, 1) +
  theme_bw() +
  geom_hline(yintercept = 0.95, linetype = "dotted") +
  scale_x_continuous(breaks = c(30, 100), labels = c(30, 100), limits = c(10, 120)) +
  labs(title = "Average Coverage For Basic Confidence Intervals"); basic

norm <- results %>% 
  filter(CI == "norm") %>% # normal
  ggplot(mapping = aes(x = C, y = Coverage, colour = N)) +
  geom_point() +
  geom_errorbar(aes(ymin = mincov, ymax = maxcov, colour = N, alpha = .9)) +
  scale_alpha(guide = "none") +
  geom_line() +
  facet_grid(norm ~ boottype) +
  ylim(0, 1) +
  theme_bw() +
  geom_hline(yintercept = 0.95, linetype = "dotted") +
  scale_x_continuous(breaks = c(30, 100), labels = c(30, 100), limits = c(10, 120)) +
  labs(title = "Average Coverage For Normal Confidence Intervals"); norm


# Appendix Table ----------------------------------------------------------

results |> 
  select(-c(X, converged_reps, nonconverge_prop, mincov, maxcov)) |> 
  rename("Residual Normality" = norm,
         "Bootstrapping Type" = boottype,
         "Confidence Interval Type" = CI,
         "f1 Coverage" = f1cov,
         "f2 Coverage" = f2cov,
         "v Coverage" = vcov,
         "m Coverage" = mcov,
         "Average Coverage" = Coverage) |> 
  write.table("appendix.txt", sep = ",", row.names = F)


