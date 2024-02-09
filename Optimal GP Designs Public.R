#*******************************************************************************
#* The following R code is a step-by-step demonstration of the ideas appearing *
#* in the paper "Optimal Designs for the Gaussian Processes Model via Spectral *
#*********** Decomposition", by Ofir Harari and David M. Steinberg *************
#*******************************************************************************
#************************ Written by Ofir Harari, 2013 *************************
#*******************************************************************************



#*******************************************************************************
# Before running the code, make sure you have the following packages installed *
#*******************************************************************************
library(rgl)
library(splines)
library(lhs)
library(shape)
library(lattice)
library(grDevices)
library(stats)
#*******************************************************************************



#*******************************************************************************
#*********** The following code generates 2D IMSPE Nearly-optimal **************
#************ designs via the Karhunen-Loeve decomposition of GPs **************
#*********** first run all the functions, then choose your parameters **********
#************* and run the simulation, one paragraph after another *************
#*******************************************************************************



#*******************************************************************************
#************************* Beginning of functions ******************************
#*******************************************************************************


#*******************************************************************************
#* A technical function for filled contour plots
#*******************************************************************************
filled.contour3 = function(x = seq(0, 1, length.out = nrow(z)),
                           y = seq(0, 1, length.out = ncol(z)), z, 
                           xlim = range(x, finite = TRUE), 
                           ylim = range(y, finite = TRUE), 
                           zlim = range(z, finite = TRUE), 
                           levels = pretty(zlim, nlevels), nlevels = 20, 
                           color.palette = cm.colors, 
                           col = color.palette(length(levels) - 1), 
                           plot.title, plot.axes, 
                           key.title, key.axes, asp = NA, xaxs = "i", 
                           yaxs = "i", las = 1, 
                           axes = TRUE, frame.plot = axes,mar, ...) {
  
  if (missing(z)) {
    if (!missing(x)) {
      if (is.list(x)) {
        z <- x$z
        y <- x$y
        x <- x$x
      }
      else {
        z <- x
        x <- seq.int(0, 1, length.out = nrow(z))
      }
    }
    else stop("no 'z' matrix specified")
  }
  else if (is.list(x)) {
    y <- x$y
    x <- x$x
  }
  if (any(diff(x) <= 0) || any(diff(y) <= 0)) 
    stop("increasing 'x' and 'y' values expected")
  plot.new()
  plot.window(xlim, ylim, "", xaxs = xaxs, yaxs = yaxs, asp = asp)
  if (!is.matrix(z) || nrow(z) <= 1 || ncol(z) <= 1) 
    stop("no proper 'z' matrix specified")
  if (!is.double(z)) 
    storage.mode(z) <- "double"
  .filled.contour(as.double(x), as.double(y), z, as.double(levels), 
                  col = col)
  if (missing(plot.axes)) {
    if (axes) {
      title(main = "", xlab = "", ylab = "")
      Axis(x, side = 1)
      Axis(y, side = 2)
    }
  }
  else plot.axes
  if (frame.plot) 
    box()
  if (missing(plot.title)) 
    title(...)
  else plot.title
  invisible()
}




#*******************************************************************************
# The large matrix R.tilde for the Fredholm Integral Equation numerical solution 
#*******************************************************************************
corr.matrix = function(theta, x){
  n = length(x)
  d = length(theta)
  R1 = matrix(0, nrow = n, ncol = n)
  R2 = matrix(0, nrow = n, ncol = n)
  
  for(i in 1:n)
  {
    for(j in 1:n)
    {
      R1[i,j] = exp(-theta[1]*abs(x[i]-x[j])^2)
      R2[i,j] = exp(-theta[2]*abs(x[i]-x[j])^2)
    }
  }
  
  return(list(R1, R2))
}



#*******************************************************************************
#* The correlation matrix R evaluated at the design D. Lambda is the parameter 
#* for the nugget term
#*******************************************************************************
corr.matrix.small = function(theta, D, lambda.nugget)
{
  n = dim(D)[1]
  d = dim(D)[2]
  nugget.mat = lambda.nugget*diag(n)
  Theta = diag(theta)	
  U = matrix(apply(D^2%*%Theta, 1, sum), nrow = n, ncol = n ,byrow=F)
  V = -2*D%*%Theta%*%t(D)
  Dist = U + t(U) + V
  
  return(exp(-Dist)+ nugget.mat)
}



#*******************************************************************************
#* Cross correlations matrix (for the Batch-Sequential section) 
#*******************************************************************************
cross.corr.matrix = function(theta, D.new, D.old){
  n1 = dim(D.new)[1]
  n2 = dim(D.old)[1]
  Theta = diag(theta)
  
  U = matrix(apply(D.new^2%*%Theta, 1, sum), nrow = n1, ncol = n2 ,byrow=F)
  V = -2*D.new%*%Theta%*%t(D.old)
  W = matrix(apply(D.old^2%*%Theta, 1, sum), nrow = n1, ncol = n2 ,byrow=T)
  Dist = U + V + W
  
  return(exp(-Dist))
}




#*******************************************************************************
#* Fredholm Integral Equation numerical solution
#*******************************************************************************
Fredholm.Solution = function(theta, n, alpha, ends, design.size, lambda.nugget, 
                             for.err){
  x = (((-n):(n-1))/n+1/(2*n))*ends[2] #grid 
  R = corr.matrix(theta, x)
  
  decomp1 = eigen(R[[1]], symmetric=1)
  decomp2 = eigen(R[[2]], symmetric=1)
  
  lambda1 = decomp1$values/(2*n/(ends[2]-ends[1]))
  lambda2 = decomp2$values/(2*n/(ends[2]-ends[1]))
  lambda = lambda1%*%t(lambda2)
  size = dim(lambda)[1]
  
  lambda.temp = sort(lambda, decreasing = T)
  total.energy = sum(lambda^2/(lambda + lambda.nugget))
  M = which(cumsum(lambda.temp^2/(lambda.temp+lambda.nugget))/total.energy >= 
              (1-alpha))[1] #Finding the truncation index
  #if(lambda.nugget==0 & for.err==0) M = min(M, design.size)
  lambda.large = lambda.temp[1:M] #Retaining first M eigenvalues
  
  large.indices = order(lambda, decreasing = T)[1:M]
  first.index = large.indices-floor(large.indices/size)*size
  second.index = floor(large.indices/size)+1
  list.of.pairs = cbind(first.index, second.index, lambda.large)
  #Indices of combinations for the largest eigenvalues  
  
  phi1 = decomp1$vectors[,list.of.pairs[,1]]*sqrt(2*n/(ends[2]-ends[1])) #eigenvectors for the first 1D process
  phi2 = decomp2$vectors[,list.of.pairs[,2]]*sqrt(2*n/(ends[2]-ends[1])) #eigenvectors for the second 1D process
  integrals.1 = apply(phi1, 2, mean)*(ends[2]-ends[1])
  integrals.2 = apply(phi2, 2, mean)*(ends[2]-ends[1])
  Integral.vec = integrals.1*integrals.2 #vector of integrals (for the unknown intercept problem)
  
  return(list(x=x, list.of.pairs=list.of.pairs, lambda.large=lambda.large, 
              phi1=phi1, phi2=phi2, Integral.vec=Integral.vec))
}



#*******************************************************************************
#* An auxiliary function to help generating spline models for the evaluation of 
#* the eigenfunctions at sites not in the original grid
#*******************************************************************************
phi.interp = function(i, j, u, phi1, phi2){	
  if(i==1) s = interpSpline(u, phi1[,j])
  else  s = interpSpline(u, phi2[,j])
  
  return(s)
}



#*******************************************************************************
#* Evaluation of the eigenfunctions via product of two univariate spline 
#* predictions
#*******************************************************************************
predict.phi = function(j, x.new, phi1.splines, phi2.splines){
  predict(phi1.splines[[j]], x.new[,1])$y*predict(phi2.splines[[j]], x.new[,2])$y
}



#*******************************************************************************
#* IMSPE evaluation for the simple (known intercept) model 
#*******************************************************************************
IMSPE = function(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                 lambda.nugget){
  d = length(theta)
  D = matrix(D, ncol = d)
  n = dim(D)[1]	
  volume = (ends[2]-ends[1])^d*(1+lambda.nugget)
  R = corr.matrix.small(theta, D, lambda.nugget)
  R.Inv = solve(R)
  phi.matrix = sapply(1:M, predict.phi, x.new=D, phi1.splines=phi1.splines, 
                      phi2.splines=phi2.splines)
  
  volume - sum(phi.matrix*R.Inv%*%phi.matrix%*%diag(lambda^2))
}




#*******************************************************************************
#* Covariance matrix for the (known intercept) model
#*******************************************************************************
covar = function(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                 lambda.nugget){
  d = length(theta)
  D = matrix(D, ncol = d)
  n = dim(D)[1]	
  R = corr.matrix.small(theta, D, lambda.nugget)
  R.Inv = solve(R)
  phi.matrix = sapply(1:M, predict.phi, x.new=D, phi1.splines=phi1.splines, 
                      phi2.splines=phi2.splines)
  Lambda = diag(lambda)
  A = phi.matrix%*%Lambda
  B = R.Inv%*%A
  c = apply(B, 2, sum)
  Sigma = Lambda - t(B)%*%A + c%*%t(c)/sum(R.Inv)
  
  return(Sigma)
}



#*******************************************************************************
#* Batch Sequential IMSPE
#*******************************************************************************
IMSPE.Batch.seq = function(D.new, D.old, phi.old, R.old, R.Inv.old, Lambda, 
                           theta, phi1.splines, phi2.splines, lambda.nugget){
  d = length(theta)
  D.new = matrix(D.new, ncol = d)
  M = dim(phi.old)[2]
  R.new = corr.matrix.small(theta, D.new, lambda.nugget)
  R.Inv.new = solve(R.new)
  R.cross = cross.corr.matrix(theta, D.new, D.old)
  Q1 = R.new - R.cross%*%R.Inv.old%*%t(R.cross)
  Q2 = R.old - t(R.cross)%*%R.Inv.new%*%R.cross
  volume = (ends[2]-ends[1])^d*(1+lambda.nugget)
  phi.new = sapply(1:M, predict.phi, x.new=D.new, phi1.splines=phi1.splines, 
                   phi2.splines=phi2.splines)
  first = (t(phi.new) - t(phi.old)%*%R.Inv.old%*%t(R.cross))%*%solve(Q1)%*%phi.new
  second = (t(phi.old) - t(phi.new)%*%R.Inv.new%*%R.cross)%*%solve(Q2)%*%phi.old
  
  return(volume - sum(diag(diag(Lambda^2)%*%(first + second))))
}



#*******************************************************************************
#* IMSPE evaluation for the advanced (unknown intercept) model
#*******************************************************************************
IMSPE.advanced = function(D, theta, ends, M, lambda, Integral.vec, phi1.splines, 
                          phi2.splines,lambda.nugget){
  d = length(theta)
  D = matrix(D, ncol = d)
  n = dim(D)[1]
  volume = (ends[2]-ends[1])^d*(1+lambda.nugget)
  R = corr.matrix.small(theta, D, lambda.nugget)
  R.Inv = solve(R)
  phi.matrix = sapply(1:M, predict.phi, x.new = D, phi1.splines=phi1.splines, 
                      phi2.splines=phi2.splines)
  Lambda = diag(lambda)
  A = phi.matrix%*%Lambda
  B = R.Inv%*%A
  c = apply(B, 2, sum)
  s = sum(R.Inv)
  gamma = Integral.vec
  IMSPE = volume - sum(diag(t(A)%*%B)) + (volume - 2*t(c)%*%gamma + t(c)%*%c)/s
  
  return(IMSPE)
}



#*******************************************************************************
#* A-optimality criterion evaluation for the advanced (unknown intercept) model
#*******************************************************************************
A.advanced = function(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                      lambda.nugget){
  A = sum(diag(covar(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                     lambda.nugget)))
  
  return(as.numeric(A))
}



#*******************************************************************************
#* Finding the IMSPE-optimal design for the simple model
#*******************************************************************************
IMSPE.optim = function(n, d, epsilon, theta, n.starts, ends, M, lambda, 
                       phi1.splines, phi2.splines,lambda.nugget){
  vals = rep(0, n.starts)
  designs = list()
  IMSPE.univar = function(D){
    IMSPE(D, theta, ends, M, lambda, phi1.splines, phi2.splines, lambda.nugget)
  }
  
  for(k in 1:n.starts)
  {
    start = c(ends[1] + (ends[2]-ends[1])*maximinLHS(n,d))
    optimum = optim(start, IMSPE.univar, method = "L-BFGS-B", 
                    lower = rep(ends[1],n*d), upper = rep(ends[2],n*d))
    D.optim = matrix(optimum$par, ncol = d)
    IMSPE.optim = optimum$value
    designs[[k]] = D.optim
    vals[k] = IMSPE.optim
  }
  
  min.val = vals[which.min(vals)]
  best.design = designs[[which.min(vals)]]
  
  return(list(Design = best.design, IMSPE = min.val))
}



#*******************************************************************************
#* Finding the IMSPE-optimal Batch-Sequential design
#*******************************************************************************
IMSPE.optim.Batch = function(d, n.old, n.new, n.starts, D.old, phi.old, R.old, 
                             R.Inv.old, epsilon, theta, ends, Lambda, 
                             phi1.splines, phi2.splines, lambda.nugget){
  M = length(Lambda)
  
  vals = rep(0, n.starts)
  designs = list()
  
  IMSPE.univar.Batch = function(D.new)
  {
    IMSPE.Batch.seq(D.new, D.old, phi.old, R.old, R.Inv.old, Lambda, theta, 
                    phi1.splines, phi2.splines, lambda.nugget)
  }
  
  for(k in 1:n.starts)
  {
    start = c(ends[1] + (ends[2]-ends[1])*maximinLHS(n.new,d))
    optimum = optim(start, IMSPE.univar.Batch, method = "L-BFGS-B", 
                    lower = rep(ends[1],n*d), upper = rep(ends[2],n*d))
    D.optim = matrix(optimum$par, ncol = d)
    IMSPE.optim = optimum$value
    designs[[k]] = D.optim
    vals[k] = IMSPE.optim
  }
  
  min.val = vals[which.min(vals)]
  best.design = designs[[which.min(vals)]]
  
  return(list(Design = D.optim, IMSPE = IMSPE.optim))
}



#*******************************************************************************
#* Finding the IMSPE-optimal design for the advanced model
#*******************************************************************************
IMSPE.optim.advanced = function(start, n, d, epsilon, theta, ends, M, lambda, 
                                Integral.vec, phi1.splines, phi2.splines, 
                                lambda.nugget){
  IMSPE.univar.advanced = function(D){
    IMSPE.advanced(D, theta, ends, M, lambda, Integral.vec, phi1.splines, 
                   phi2.splines, lambda.nugget)
  }
  
  optimum = optim(start, IMSPE.univar.advanced, method = "L-BFGS-B", 
                  lower = rep(-1,n*d), upper = rep(1,n*d))
  D.optim = matrix(optimum$par, ncol = d)
  Lambda = diag(lambda)
  R = corr.matrix.small(theta, D.optim, lambda.nugget)
  R.Inv = solve(R)
  s = sum(R.Inv)
  phi.matrix = sapply(1:M, predict.phi, x.new = D.optim, 
                      phi1.splines=phi1.splines, phi2.splines=phi2.splines)
  a = apply(Lambda%*%t(phi.matrix)%*%R.Inv, 1, sum)
  A = a%*%t(a)/s
  diag(A) = -diag(A)
  varcov = Lambda - Lambda%*%t(phi.matrix)%*%R.Inv%*%phi.matrix%*%Lambda - A 
  IMSPE.optim = optimum$value
  
  return(list(Design = D.optim, IMSPE = IMSPE.optim, varcov = varcov))
}



#*******************************************************************************
#* Finding the A-optimal design for the advanced model
#*******************************************************************************
A.optim.advanced = function(start, n, d, epsilon, theta, ends, M, lambda, 
                            phi1.splines, phi2.splines, lambda.nugget){
  A.univar.advanced = function(D){
    A.advanced(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
               lambda.nugget)
  }
  
  optimum = optim(start, A.univar.advanced, method = "L-BFGS-B", 
                  lower = rep(-1,n*d), upper = rep(1,n*d))
  D.optim = matrix(optimum$par, ncol = d)
  varcov = covar(D.optim, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                 lambda.nugget) 
  A.optim = optimum$value
  
  return(list(Design = D.optim, A = A.optim, varcov = varcov))
}



#*******************************************************************************
#* Finding the D-optimal design for the advanced model
#*******************************************************************************
D.optim.advanced = function(start, n, d, epsilon, theta, ends, M, lambda, 
                            phi1.splines, phi2.splines, lambda.nugget){
  D.univar.advanced = function(D){
    Sigma = 15*covar(D, theta, ends, M, lambda, phi1.splines, phi2.splines, 
                     lambda.nugget)
    
    return(log(det(Sigma)))
  }
  
  optimum = optim(start, D.univar.advanced, method = "L-BFGS-B",
                  lower = rep(-1,n*d), upper = rep(1,n*d))
  D.optim = matrix(optimum$par, ncol = d)	
  
  return(D.optim)
}



#*******************************************************************************
#* Checking how close the optimum of the simple model is to the optimum of the 
#* advanced model
#*******************************************************************************
Criteria.comp = function(D1, D2, Integral.vec, theta, ends, lambda.large, 
                         phi1.splines, phi2.splines, lambda.nugget){
  M = length(lambda.large)
  IMSPE1 = IMSPE.advanced(D1, theta, ends, M, lambda.large, Integral.vec, 
                          phi1.splines, phi2.splines, lambda.nugget)
  IMSPE2 = IMSPE.advanced(D2, theta, ends, M, lambda.large, Integral.vec, 
                          phi1.splines, phi2.splines, lambda.nugget)
  delta = IMSPE2 - IMSPE1
  cat(paste("Advanced IMSPE for the known intercept optimum: ", IMSPE2, "\n"))
  cat(paste("Advanced IMSPE for the unknown intercept optimum: ", IMSPE1, "\n"))
  cat(paste("Delta: ", delta, "\n"))
}



#*******************************************************************************
#* Error Analysis for the simple model
#*******************************************************************************
error.analysis = function(D, theta, trunc_Num, n, lambda.nugget){
  design.size = dim(D)[1]
  fred = Fredholm.Solution(theta, n, 1e-6, c(-1,1), 
                           design.size, lambda.nugget, 1)
  lambda.large = fred$lambda.large
  total.energy = sum(lambda.large^2/(lambda.large + lambda.nugget))
  Energy.Retained = sum((lambda.large[1:trunc_Num])^2/(lambda.large[1:trunc_Num] + lambda.nugget))/total.energy
  phi1 = fred$phi1
  phi2 = fred$phi2
  M = length(lambda.large)
  x = fred$x
  lim = min(design.size,trunc_Num)
  
  phi1.spl = lapply(1:M, phi.interp, i=1, u=x, phi1=phi1, phi2=phi2)
  phi2.spl = lapply(1:M, phi.interp, i=2, u=x, phi1=phi1, phi2=phi2)
  
  phi.matrix = sapply(1:M, predict.phi, x.new=D, phi1.splines=phi1.spl, 
                      phi2.splines=phi2.spl)
  R = corr.matrix.small(theta, D, lambda.nugget)
  R.Inv = solve(R)
  
  if(lambda.nugget==0){
    eq1 = as.expression(bquote(k<=.(lim)))
    eq2 = as.expression(bquote(k>.(lim)))
    dev.new(height = 6, width = 8)
    par(mar = c(4,6,4,1))
    temp = lambda.large*diag(t(phi.matrix)%*%R.Inv%*%phi.matrix)
    plot(temp, cex.lab = 1.6, axes = 0, xlab = '', ylab = '')
    axis(1, pos = -0.02, at = c(-100, 2*(0:round(M/2))+1))
    axis(2, pos = 0, at = c(.2*c(-1:5),10))
    text(-5.5, 1.1, expression(lambda[k]*phi[k]^T*R^{-1}*phi[k]), 
         cex = 1.6, xpd = T)
    mtext('k', 1, 1.5, cex = 1.6)
    lines(c(lim, lim), c(-.02,1), lty = 3)
    points(temp[1:lim], pch = 19, cex = 1.3)
    points((lim+1):length(temp),temp[(lim+1):length(temp)], pch = 21, 
           cex = 1.3, bg = 'light gray')
    legend('topright', c(eq1, eq2), pt.bg = c('black', 'light gray'), pch = 21, 
           pt.cex = 1.5, cex = 1.5)
  }
  
  W = diag(lambda.large^2)%*%t(phi.matrix)%*%R.Inv%*%phi.matrix
  
  dev.new(width = 8, height = 6)
  par(mar = c(3,5,2,3))
  plot(cumsum(diag(W)), type = 'l', lwd = 2, axes = 0, xlab = '', ylab = '', 
       ylim = c(W[1,1], 4.3))
  axis(1, pos = W[1,1], at = 3*c(0:round(M/3)))
  axis(2, pos = 0, at = c(0:4))
  text(M+2.5, W[1,1]-.2, "k", xpd = 1, cex = 1.6)
  text(0, 4.3, expression(sum(lambda[j]^2*phi[j]^T*(R+lambda*I)^{-1}*phi[j], 
                              j==1, k)), 
       xpd = 1, cex = 1.4)
  lines(rep(trunc_Num,2), c(diag(W)[1], sum(diag(W)[1:trunc_Num])), 
        lty = 2, col = 2, lwd = 2)
  
  Trunc_Criterion = sum((diag(W)[1:trunc_Num])^2/(diag(W)[1:trunc_Num]+lambda.nugget))
  Criterion = sum((diag(W))^2/(diag(W)+lambda.nugget))
  error = (Criterion-Trunc_Criterion)/Criterion
  cat("Relative truncation error \n")
  cat(paste("for ", design.size, " inputs (M=",trunc_Num,"):\n", sep = ''))
  cat(paste(error, "\n\n"))
  cat("Asymptotic relative error:\n")
  cat(paste(1-Energy.Retained, "\n\n"))
  
  return(error)
}
#*******************************************************************************



#*******************************************************************************
#* Rescaling a design to the [-1,1]^2 square and recalculating IMSPE
#*******************************************************************************
rescale = function(D, ends, theta, M.permanent, lambda.permanent, 
                   Integral.vec.permanent, phi1.splines, phi2.splines, 
                   is.simple)
{
  D = 2*D/(ends[2]-ends[1])
  IMSPE = ifelse(is.simple==1, 
                 IMSPE(c(D), theta, c(-1,1), M.permanent, lambda.permanent, 
                       phi1.splines.permanent, phi2.splines.permanent, 
                       lambda.nugget),
                 IMSPE.advanced(c(D), theta, c(-1,1), M.permanent, 
                                lambda.permanent, Integral.vec.permanent, 
                                phi1.splines.permanent, 
                                phi2.splines.permanent, lambda.nugget))
  A.criterion = A.advanced(c(D), theta, c(-1,1), M.permanent, 
                           lambda.permanent, phi1.splines.permanent, 
                           phi2.splines.permanent, lambda.nugget)
  D.criterion = log(det(covar(c(D), theta, c(-1,1), M.permanent, 
                              lambda.permanent, phi1.splines.permanent, 
                              phi2.splines.permanent, lambda.nugget)))
  
  return(list(Design = D, IMSPE = IMSPE, A.criterion = A.criterion, 
              D.criterion = D.criterion))
}



#*******************************************************************************
#* Plot function for designs
#*******************************************************************************
plot.design = function(D, IMSPE, batch.size){
  size = dim(D)[1] - batch.size
  
  h = 10
  w = 10*as.numeric(batch.size==0) + 12*as.numeric(batch.size>0)
  
  mars = c(5,6,5,5)*as.numeric(batch.size==0) + c(5,6,5,11)*as.numeric(batch.size>0)
  dev.new(height = h, width = w)
  
  par(mar = mars)
  plot(D[1:size,], xlab = expression(X[1]), ylab = expression(X[2]), cex = 3, 
       axes = 0, cex.lab = 2.5, pch = 19, 
       xlim = c(-1.05,1.05), ylim = c(-1.05,1.05))
  lines(c(-1.05,1.05,1.05,-1.05,-1.05), c(-1.05,-1.05,1.05,1.05,-1.05), 
        lwd = 3, col = 4)
  axis(1, pos = -1.05, at = c(-1,-.5,0,.5,1), cex.axis = 1.5)
  axis(2, pos = -1.05, at = c(-1,-.5,0,.5,1), cex.axis = 1.5)
  if(batch.size == 0){
    title(main = paste("Size ", size, " design, IMSPE=", round(IMSPE,5), 
                       sep = ''), cex.main = 2)
  } else{
    points(D[(size+1):(dim(D)[1]),], lwd = 2.5, cex=3, bg = 'light gray', 
           pch = 21)
    title(main = paste("Size ", size, "+", batch.size, " design, IMSPE=", 
                       round(IMSPE,5), sep = ''), 
          cex.main = 2)
    legend(1.05, .15, c("1st Batch", "2nd Batch"), pch = c(19,21), xpd=1, 
           pt.cex=2.5, pt.lwd=2.5, cex = 2, pt.bg = c(1, 'light gray'))
  }
  
}


#*******************************************************************************
#*******************************************************************************
#***************************** End of functions ********************************
#*******************************************************************************
#*******************************************************************************



#*******************************************************************************
#************************* Simulation Starts Here!!!!!!! ***********************
#* Be cautious about the parameters you choose:
#* Small thetas will make the correlation matrix nearly singular
#* Large thetas will require many terms in the expansion - runtime!
#* Dimension parameter d (is fixed) for now, do not change it
#* Batch sequential designs are only recommended for relatively small designs 
#* (and batches). 
#* Large n.starts.batch can make it pretty long
#* Do not change "ends". It recalculates the interval length to avoid
#* singularity, and then the resulting design is shrunk back to the [-1,1]^2
#* square. 
#* The parameter "design.size" should not exceed 50 if you want to see the end 
#* of it, and alpha should be at least 5e-2 for designs of size larger than 40.
#*******************************************************************************
#*******************************************************************************



#*******************************************************************************
#* Parameters for the simulation
#*******************************************************************************
theta = c(1,2) #Correlation parameters
lambda.nugget = 0.1 #Nugget parameter (error_var/process_var)
design.size = 8  #Number of inputs in the experimental design 
ends = c(-1,1)*ifelse(lambda.nugget > 0, 1, max(1, sqrt(design.size/15)))  #ends of experimental interval (for the 1d sub-processes)
alpha = 5e-3    #percentage of energy loss afforded
n = max(25, round(25*ends[2]))        #half-grid number of points  
n.starts = 1      #Number of starting positions for the optimization procedure
n.starts.batch = 4  #Number of starting positions for the Batch sequential design
d = 2  #problem dimension
Batch.Size = 7



#*******************************************************************************
#* Solving the Integral Equation (for display purposes, on the [-1,1] interval
#*******************************************************************************
fred = Fredholm.Solution(theta, n, alpha, c(-1,1), design.size, 
                         lambda.nugget, 0)
x = fred$x
list.of.pairs = fred$list.of.pairs
lambda.large.permanent = fred$lambda.large
M.permanent = length(lambda.large.permanent)
phi1 = fred$phi1
phi2 = fred$phi2
M.permanent = length(lambda.large.permanent)
Integral.vec.permanent = fred$Integral.vec

phi1.splines.permanent = lapply(1:M.permanent, phi.interp, i=1, u=x, 
                                phi1=phi1, phi2=phi2)
phi2.splines.permanent = lapply(1:M.permanent, phi.interp, i=2, u=x, 
                                phi1=phi1, phi2=phi2)



#*******************************************************************************
#* Plotting eigenvalues
#******************************************************************************* 
dev.new(width = 9, height = 6)
par(mar=c(3,5,3,1))
plot(log(lambda.large.permanent), pch = 19, axes = 0, xlab = '', ylab = '', cex = 2, 
     xlim = c(0, length(lambda.large.permanent)+1))
title(main = "Eigenvalues vs. Index", cex.main = 1.6)
axis(1, pos = min(log(lambda.large.permanent)), at = c(0:M.permanent, 500))
axis(2, pos = .2, at = c(-10:2))
text(-1, max(log(lambda.large.permanent))+.2, expression(log*lambda[k]), cex = 1.6, xpd = 1)
text(M.permanent + 1, min(log(lambda.large.permanent))-.3, 'k', cex = 1.6, xpd = 1)



#*******************************************************************************
#* Plotting eigenfunctions and generating a realization form the process
#*******************************************************************************
eigenfunc = list()
Kar_Loe_Reconst = 0
coeffs = rnorm(M.permanent)

dev.new(width = 12, height = 8)
par(mfrow = c(2,3), mar = c(5,5,3,3))


for(i in 1:M.permanent){
  eigenfunc[[i]] = phi1[,i]%*%t(phi2[,i])
  
  if(i <= 6){
    z = eigenfunc[[i]]
    filled.contour3(x, x, z, color=femmecol, xlab = expression(X[1]), 
                    ylab = expression(X[2]), cex.lab = 1.6)
    contour(x, x, eigenfunc[[i]],add=T)
    title(main = substitute(paste("Eigenfunction #", i, " , ", 
                                  lambda, " = ", lamb), 
                            list(i=i, lamb = round(list.of.pairs[i,3], 4))), 
          cex.main = 1.4)
  }
  
  Kar_Loe_Reconst = Kar_Loe_Reconst + sqrt(list.of.pairs[i,3])*coeffs[i]*eigenfunc[[i]]
}

open3d(windowRect=c(100,100,1000,750))
bg3d("white")
material3d(col="black")	

persp3d(x, x, Kar_Loe_Reconst, col = "light green", xlim = range(x), 
        ylim = range(x), zlim = range(Kar_Loe_Reconst, na.rm = TRUE),
        theta=35, phi=20, axes = 0, xlab = "", ylab = "", zlab = "", 
        smooth=FALSE)


dev.new(height = 6, width = 6)
par(mar = c(5,5,5,2))
filled.contour3(x, x, Kar_Loe_Reconst, color = femmecol, 
                xlab = expression(X[1]), ylab = expression(X[2]), cex.lab = 1.6)
contour(x, x, Kar_Loe_Reconst, add = T)



#*******************************************************************************
#* Solving the Integral Equation (this time for real
#*******************************************************************************
fred = Fredholm.Solution(theta, n, alpha, ends, design.size, lambda.nugget, 0)
x = fred$x
list.of.pairs = fred$list.of.pairs
lambda.large = fred$lambda.large
phi1 = fred$phi1
phi2 = fred$phi2
Integral.vec = fred$Integral.vec
M = length(lambda.large)



#*******************************************************************************
#* Preparing spline models to evaluate the eigenfunctions at new inputs
#*******************************************************************************
phi1.splines = lapply(1:M, phi.interp, i=1, u=x, phi1=phi1, phi2=phi2)
phi2.splines = lapply(1:M, phi.interp, i=2, u=x, phi1=phi1, phi2=phi2)



#*******************************************************************************
#* Generating IMSPE-optimal design for the simple model (takes a while)
#*******************************************************************************
ptm = proc.time()
D.simple = IMSPE.optim(design.size, d, epsilon, theta, n.starts, ends, M, 
                       lambda.large, phi1.splines, phi2.splines, lambda.nugget)
proc.time()-ptm
D.simple.rescaled = rescale(D.simple$Design, ends, theta, M.permanent, 
                            lambda.large.permanent, Integral.vec.permanent, 
                            phi1.splines.permanent, phi2.splines.permanent, 1)

plot.design(D.simple.rescaled$Design, D.simple.rescaled$IMSPE, 0)



#*******************************************************************************
#* Error Analysis for the simple model
#*******************************************************************************
r = error.analysis(D.simple.rescaled$Design, theta, M.permanent, n, 
                   lambda.nugget)


#*******************************************************************************
#* Generating IMSPE-optimal design for the advanced model (using the optimum of 
#* the simple model as a starting point)
#*******************************************************************************
start = c(D.simple$Design)
D.advanced = IMSPE.optim.advanced(start, design.size, d, epsilon, theta, ends, 
                                  M, lambda.large, Integral.vec, phi1.splines, 
                                  phi2.splines, lambda.nugget)
D.advanced.rescaled = rescale(D.advanced$Design, ends, theta, M.permanent, 
                              lambda.large.permanent, Integral.vec.permanent, 
                              phi1.splines.permanent, phi2.splines.permanent, 0)



#*******************************************************************************
#* Plotting both designs together
#*******************************************************************************
dev.new(height = 8, width = 8)
par(mar = c(5,5,3,3))
plot(D.simple.rescaled$Design, pch = 19, cex = 1.5, xlab = expression(X[1]), 
     ylab = expression(X[2]), xlim = ends,
     ylim = c(-1,1), cex.lab = 2)
points(D.advanced.rescaled$Design, lwd = 2, cex = 3)



#*******************************************************************************
#* Plotting the prior and posterior variances of the (infinitely many)
#* regression coefficients
#*******************************************************************************
post.vars = diag(D.advanced$varcov)
dev.new(width = 12, height = 7)
par(mar = c(4,6,4,1))
plot(log(lambda.large), pch = 19, axes = 0, xlab = '', ylab = '', cex = 1.6, 
     ylim = c(min(log(post.vars)), max(log(lambda.large))))
axis(1, at = c(-1, 1:17, 20), cex.axis =1.5)
axis(2, at = seq(-1000, 10, by = 2), cex.axis =1.5)
points(log(post.vars), xpd = T, pch = 21, lwd = 2, cex = 3, bg = 'light gray')
points(log(lambda.large), pch = 19, cex = 1.6)
mtext("k", 1, 2.5, cex = 1.6)
text(expression(paste(log, "Var[", beta[k], "|y]")), x=-.5, 
     y = log(lambda.large[1])+1, 
     cex = 1.6, xpd = T)
title(main = "Prior and Posterior Variances", cex.main = 2)
legend('topright', c("Prior", "Posterior"), pch = c(19,21), pt.lwd = 2, 
       cex = 1.5, pt.cex = 2.5, pt.bg = c(1, 'light gray'))



#*******************************************************************************
#* Generating A-optimal design for the advanced model (using the optimum of the 
#* simple model as a starting point)
#*******************************************************************************
if(lambda.nugget > 0){
  start = c(D.advanced$Design)
  D.A.opt = A.optim.advanced(start, design.size, d, epsilon, theta, ends, M, 
                             lambda.large, phi1.splines, phi2.splines, 
                             lambda.nugget)
  D.A.opt.rescaled = rescale(D.A.opt$Design, ends, theta, M.permanent, 
                             lambda.large.permanent, Integral.vec.permanent, 
                             phi1.splines.permanent, phi2.splines.permanent, 0)
}
#*******************************************************************************



#*******************************************************************************
#* Plotting IMSPE and A-optimal designs
#*******************************************************************************
if(lambda.nugget > 0){
  dev.new(height = 8, width = 16)
  par(mfrow = c(1,2), mar = c(5,5,3,3))
  plot(D.advanced.rescaled$Design, pch = 19, cex = 3, xlab = expression(X[1]), 
       ylab = expression(X[2]), xlim = c(-1,1), ylim = c(-1,1), cex.lab = 2)
  title(main = "IMSPE-optimal", cex.main = 2)
  plot(D.A.opt.rescaled$Design, lwd = 2, pch = 19, cex = 3, 
       xlab = expression(X[1]), ylab = expression(X[2]), xlim = c(-1,1), 
       ylim = c(-1,1), cex.lab = 2)
  title(main = "A-optimal", cex.main = 2)
}



#*******************************************************************************
#* Plotting the prior and posterior variances of the (infinitely many) 
#* regression coefficients
#*******************************************************************************
if(lambda.nugget > 0){
  post.vars = diag(D.A.opt$varcov)
  post.vars2 = diag(D.advanced$varcov)
  dev.new(width = 12, height = 7)
  par(mar = c(4,6,4,1))
  plot(log(lambda.large), pch = 19, axes = 0, xlab = '', ylab = '', cex = 1.6, 
       ylim = c(min(c(log(post.vars), log(post.vars2))), 
                max(log(lambda.large))))
  axis(1, at = c(-1, 1:17, 20), cex.axis =1.5)
  axis(2, at = seq(-1000, 10, by = 2), cex.axis =1.5)
  points(log(post.vars), xpd = T, pch = 21, lwd = 2, cex = 3, bg = 'light gray')
  points(log(lambda.large), pch = 19, cex = 1.6)
  points(log(post.vars2), pch = 18, cex = 2, col = 2)
  mtext("k", 1, 2.5, cex = 1.6)
  text(expression(paste(log, "Var[", beta[k], "|y]")), x= .2, 
       y = log(lambda.large[1])+.5, 
       cex = 1.6, xpd = T)
  title(main = "Prior and Posterior Variances", cex.main = 2)
  legend('topright', c("Prior", "A-opt Posterior", "IMSPE-opt Posterior"), 
         pch = c(19,21,18), pt.lwd = 2, cex = 1.5, pt.cex = 2.5, 
         col = c(1, '1', 2), pt.bg = c(1, 'light gray', 2))
  abline(c(log(mean(post.vars)), 0), col = 1, lty = 2)
  abline(c(log(mean(post.vars2)), 0), col = 2, lty = 3)
}



#*******************************************************************************
#* Finding the deviation of the simple optimum from the advance optimum
#*******************************************************************************
Criteria.comp(D.advanced.rescaled$Design, D.simple.rescaled$Design, 
              Integral.vec.permanent, theta, c(-1,1), lambda.large.permanent, 
              phi1.splines.permanent, phi2.splines.permanent, lambda.nugget)


#*******************************************************************************
#* Generating D-optimal design for the advanced model (using the IMSPE-optimal 
#* design as a starting point)
#*******************************************************************************
if(lambda.nugget > 0)
{
  start = c(D.advanced$Design)
  D.opt = D.optim.advanced(start, design.size, d, epsilon, theta, ends, M, 
                           lambda.large, phi1.splines, phi2.splines, 
                           lambda.nugget)
  D.opt.rescaled = rescale(D.opt, ends, theta, M.permanent, 
                           lambda.large.permanent, Integral.vec.permanent, 
                           phi1.splines.permanent, phi2.splines.permanent, 0)
  
  dev.new(width = 18, height = 6)
  par(mar = c(4,5,3,2), mfrow = c(1,3))
  plot(D.opt.rescaled$Design, pch = 19, cex = 3, xlab = expression(X[1]), 
       ylab = expression(X[2]), xlim = c(-1,1), ylim = c(-1,1), cex.lab = 2)
  title(main = "D-optimal", cex.main = 2.5)
  
  par(mar = c(4,5,3,2))
  plot(D.advanced.rescaled$Design, pch = 19, cex = 3, xlab = expression(X[1]), 
       ylab = expression(X[2]), xlim = c(-1,1), ylim = c(-1,1), cex.lab = 2)
  title(main = "IMSPE-optimal", cex.main = 2.5)
  
  par(mar = c(4,5,3,2))
  plot(D.A.opt.rescaled$Design, pch = 19, cex = 3, xlab = expression(X[1]), 
       ylab = expression(X[2]), xlim = c(-1,1), ylim = c(-1,1), cex.lab = 2)
  title(main = "A-optimal", cex.main = 2.5)
}



#*******************************************************************************
#* Comparison od IMSPE, A and D-optimal Designs by all 3 criteria
#*******************************************************************************
if(lambda.nugget>0)
{
  D.A.opt.rescaled$IMSPE
  D.advanced.rescaled$IMSPE
  D.opt.rescaled$IMSPE
  
  D.A.opt.rescaled$A.criterion
  D.advanced.rescaled$A.criterion
  D.opt.rescaled$A.criterion
  
  D.A.opt.rescaled$D.criterion
  D.advanced.rescaled$D.criterion
  D.opt.rescaled$D.criterion
}



#*******************************************************************************
#* Batch Sequential design
#*******************************************************************************
if(Batch.Size > 0)
{
  D.old = D.simple$Design
  phi.old = sapply(1:M, predict.phi, x.new = D.old, phi1.splines, phi2.splines)
  R.old = corr.matrix.small(theta, D.old, lambda.nugget)
  R.Inv.old = solve(R.old)
  
  D.Batch.Seq = IMSPE.optim.Batch(d, design.size, Batch.Size, n.starts.batch, 
                                  D.old, phi.old, R.old, R.Inv.old, epsilon, 
                                  theta, ends, lambda.large, phi1.splines, 
                                  phi2.splines, lambda.nugget)
  
  D.new = D.Batch.Seq$Design
  D.new.rescaled = rescale(D.new, ends, theta, M.permanent, 
                           lambda.large.permanent, Integral.vec.permanent, 
                           phi1.splines.permanent, phi2.splines.permanent, 1)
  
  D.new = D.new.rescaled$Design
  
  #checking that the block decomposition indeed recovers the true IMSPE
  D.total = rbind(D.simple.rescaled$Design, D.new)
  IMSPE.total = rescale(D.total, ends, theta, M.permanent, 
                        lambda.large.permanent, Integral.vec.permanent, 
                        phi1.splines.permanent, phi2.splines.permanent, 1)$IMSPE
  
  IMSPE.total
  
  IMSPE.Batch.seq(c(D.new), D.simple.rescaled$Design, phi.old, R.old, R.Inv.old, 
                  lambda.large.permanent, theta, phi1.splines.permanent, 
                  phi2.splines.permanent, lambda.nugget)
  
  plot.design(D.total, IMSPE.total, Batch.Size)
}
