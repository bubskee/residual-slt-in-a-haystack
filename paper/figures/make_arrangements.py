"""Compact adaptation of residual-slt-guide figures 01-puzzle and 09-inactive-groups.

Source: scripts/make_figures.py, chain() and the corresponding figure layouts.
All three distinct depth-five cases are shown; labels follow manuscript Theorem 2.
Run from any directory with Python and matplotlib. No numerical experiment.
"""
from pathlib import Path
from fractions import Fraction
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyArrowPatch

OUT = Path(__file__).resolve().parent
plt.rcParams.update({'font.family':'serif', 'font.serif':['STIXGeneral'],
                     'mathtext.fontset':'stix', 'font.size':10,
                     'pdf.fonttype':42, 'svg.fonttype':'path'})
fig, ax = plt.subplots(figsize=(6.5,2.65))
fig.subplots_adjust(left=.015,right=.995,bottom=.04,top=.95)
ax.set(xlim=(-.8,8.35),ylim=(-.16,3.47)); ax.axis('off')
xs=[.40+j*.97 for j in range(5)]; width=.57; height=.38
ax.text(-.68,3.28,r'$w^*$',va='center')
for j,x in enumerate(xs,1):ax.text(x+width/2,3.28,str(j),ha='center',va='center',color='.35')
ax.text(6.87,3.28,r'Local $(\lambda,m)$',ha='center',va='center')

def arrow(x0,x1,y):
    ax.add_patch(FancyArrowPatch((x0,y),(x1,y),arrowstyle='-|>',mutation_scale=7,lw=.65,color='.35'))
def group(x0,x1,y,label):
    ax.plot([x0,x0,x1,x1],[y+.05,y,y,y+.05],color='.25',lw=.65)
    ax.text((x0+x1)/2,y-.04,label,ha='center',va='top',fontsize=10)

for y,j,gaps,pair in [(2.58,1,(0,4),(Fraction(13,12),1)),(1.53,2,(1,3),(Fraction(7,6),2)),(.48,3,(2,2),(Fraction(7,6),1))]:
    # Verify the shown labels by exact evaluation of the manuscript's cubic rule.
    A=lambda n: Fraction(n,6)-Fraction(max(n-3,0),12)
    assert pair==(Fraction(1,2)+sum(A(n) for n in gaps),1+sum(n==3 for n in gaps))
    ax.text(-.68,y+height/2,rf'$e_{j}$',va='center')
    arrow(-.03,xs[0],y+height/2)
    for i,x in enumerate(xs,1):
        active=i==j
        ax.add_patch(Rectangle((x,y),width,height,facecolor='.17' if active else 'white',edgecolor='.25',lw=.8))
        ax.text(x+width/2,y+height/2,'1' if active else '0',ha='center',va='center',color='white' if active else '.2',fontsize=11)
        if i<5:arrow(x+width,xs[i],y+height/2)
    arrow(xs[-1]+width,5.48,y+height/2)
    if j==1:
        ax.text(xs[0]+width/2,y-.10,r'$n_0=0$',ha='center',va='top')
    else:group(xs[0],xs[j-2]+width,y-.12,rf'$n_0={gaps[0]}$')
    group(xs[j],xs[-1]+width,y-.12,rf'$n_1={gaps[1]}$')
    ax.text(6.87,y+height/2,rf'$({pair[0]},{pair[1]})$',ha='center',va='center',fontsize=11)

fig.savefig(OUT/'active-arrangements.pdf',metadata={'Title':'Active placement changes inactive-group lengths','CreationDate':None,'ModDate':None})
fig.savefig(OUT/'active-arrangements.svg',metadata={'Date':None})
fig.savefig(OUT/'active-arrangements.png',dpi=220)
plt.close(fig)
print('Adapted figure saved; exact group lengths and local pairs verified.')
