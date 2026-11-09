"""Seeded numerical checks of the extended results, not proofs.
Running this imports verify_model, reproducing its checks and figure too.
Requirements: numpy, scipy, matplotlib.
"""
import json
import numpy as np
from scipy.integrate import quad
from scipy.special import gammainc
from verify_model import ROOT, triangle, frame
rng=np.random.default_rng(20261027)
results={'seed':20261027,'role':'Numerical cross-checks, not proofs'}
# Circulant spectrum equals the Fourier weights in the triangle criterion.
w=np.exp(2j*np.pi/3); err=0.
for _ in range(20000):
 r=rng.random(); angles=rng.uniform(-np.pi,np.pi,3);z=r*np.exp(1j*angles.sum()/3)
 eig=np.linalg.eigvalsh(triangle(r,*angles));p=(1+2*np.real(z*w**(-np.arange(3))))/3
 err=max(err,float(np.max(np.abs(eig-np.sort(3*p)))))
 assert (eig.min()>=-1e-10)==(p.min()>=-1e-10)
assert err<1e-12
results['polygon']={'samples':20000,'maximum_spectrum_error':err}
# General block vector bound, rank estimate, and weighted path estimate.
vecerr=rankerr=sparseerr=0.
for _ in range(200):
 d,m,n=2,5,4;v=[frame(m,d) for _ in range(n)]
 k=[[x.conj().T@y for y in v] for x in v]
 delta=np.maximum(0,d-np.array([[np.linalg.norm(z,'fro')**2 for z in row] for row in k]))
 x=rng.normal(size=d)+1j*rng.normal(size=d);y=rng.normal(size=d)+1j*rng.normal(size=d)
 lhs=abs(np.vdot(y,(k[0][2]-k[0][1]@k[1][2])@x))**2
 rhs=(np.linalg.norm(y)**2-np.linalg.norm(k[1][0]@y)**2)*(np.linalg.norm(x)**2-np.linalg.norm(k[1][2]@x)**2)
 vecerr=max(vecerr,float(lhs-rhs));assert lhs<=rhs+1e-9
 kk=np.block(k);lower=(n*d)**2/np.linalg.norm(kk,'fro')**2;rank=np.linalg.matrix_rank(kk,tol=1e-9)
 rankerr=max(rankerr,float(lower-rank));assert lower<=rank+1e-9
 weights=np.array([1.,5.,.6]);D=sum(weights[i]*delta[i,i+1] for i in range(3));C=sum(1/weights)
 sparseerr=max(sparseerr,float(delta.max()-C*D));assert delta.max()<=C*D+1e-9
results['block_checks']={'samples':200,'max_vector_violation':vecerr,'max_rank_violation':rankerr,'max_sparse_violation':sparseerr}
# Polar and phase-corrected QR frames have identical projectors.
err=0.
for _ in range(100):
 z=rng.normal(size=(7,3))+1j*rng.normal(size=(7,3));u,_,vh=np.linalg.svd(z,full_matrices=False);vp=u@vh
 q,r=np.linalg.qr(z);vq=q*(np.diag(r)/np.abs(np.diag(r)))[None,:]
 err=max(err,float(np.linalg.norm(vp@vp.conj().T-vq@vq.conj().T)))
assert err<1e-11
results['polar_qr_projector_error']=err
# Z5 dilation, quantitative group defect, finite-group rounding, covariance.
rounderr=coverr=deferr=0.
for _ in range(30):
 q=frame(4,4);R=[q@np.diag(np.exp(2j*np.pi*k*np.arange(4)/5))@q.conj().T for k in range(5)]
 z=np.eye(4,2,dtype=complex)+.015*(rng.normal(size=(4,2))+1j*rng.normal(size=(4,2)))
 u,_,vh=np.linalg.svd(z,full_matrices=False);V=q@u@vh;phi=[V.conj().T@r@V for r in R]
 delta=[max(0,2-np.linalg.norm(p,'fro')**2) for p in phi];eps=max(delta);assert eps<.125
 P=V@V.conj().T;A=sum(r@P@r.conj().T for r in R)/5
 val,u=np.linalg.eigh(A);Q=u[:,val>=.5]@u[:,val>=.5].conj().T;assert sum(val>=.5)==2
 val,u=np.linalg.eigh(V.conj().T@Q@V);W=Q@V@((u*val**(-.5))@u.conj().T);rho=[W.conj().T@r@W for r in R]
 assert max(np.linalg.norm(phi[k]-rho[k],2) for k in range(5))<=8*np.sqrt(eps)+1e-10
 for a in range(5):
  for b in range(5):
   defect=np.linalg.norm(phi[(a+b)%5]-phi[a]@phi[b],'fro')**2-delta[a]*delta[b]
   deferr=max(deferr,float(defect));assert defect<1e-10
   e=np.linalg.norm(rho[(a+b)%5]-rho[a]@rho[b]);rounderr=max(rounderr,float(e));assert e<1e-10
 local=[frame(2,2) for _ in range(5)]
 K=lambda i,j:local[i].conj().T@phi[(j-i)%5]@local[j]
 coc=lambda g,i:local[(g+i)%5].conj().T@local[i]
 for g in range(5):
  for i in range(5):
   for j in range(5):
    e=np.linalg.norm(K((g+i)%5,(g+j)%5)-coc(g,i)@K(i,j)@coc(g,j).conj().T)
    coverr=max(coverr,float(e));assert e<1e-10
results['group_checks']={'samples':30,'max_defect_violation':deferr,'max_rounded_multiplication_error':rounderr,'max_covariance_error':coverr}
# Exact two-frame Gamma law and concentration inequality, checked by quadrature.
rows=[];meanerr=tailerr=0.
for m in [2,3,4,6]:
 a=m-1
 for lam in [.2,1.,5.,20.,100.,300.]:
  f=lambda x:x**(a-1)*np.exp(-lam*x)
  den=quad(f,0,1,epsabs=1e-18,epsrel=1e-11)[0];num=quad(lambda x:x*f(x),0,1,epsabs=1e-18,epsrel=1e-11)[0]
  exact=a*gammainc(a+1,lam)/(lam*gammainc(a,lam));e=abs(num/den-exact);meanerr=max(meanerr,e);assert e<1e-9
  for eps in [.05,.2,.5,.9]:
   tail=quad(f,eps,1,epsabs=1e-18)[0]/den;bound=(eps/2)**(-a)*np.exp(-lam*eps/2)
   tailerr=max(tailerr,tail-bound);assert tail<=bound+1e-10
  rows.append({'m':m,'lambda':lam,'lambda_times_mean':float(lam*exact),'limit':a})
results['two_frame']={'max_mean_error':meanerr,'max_concentration_violation':tailerr,'values':rows}
results['status']='PASS'
results['not_numerically_established']=['general-graph weak convergence','general-graph Laplace asymptotics']
results['notes']='Analytic proofs cover general fixed graphs. The script tests the two-frame special case; no MCMC claims.'
(ROOT/'EXTENDED_NUMERICAL_CHECKS.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results,indent=2))
