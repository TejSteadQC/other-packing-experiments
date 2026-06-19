#!/usr/bin/env python3
"""Render cirinttt and cirinl packings in Erich Friedman's website style:
gray (#cccccc) circle fill, thin black outline, black container outline, white
background, NO center dots, NO inner triangle, NO labels.

Outputs per packing:
  <category>/figures_ef/png/n<NN>.png   (small raster, ~200px, borders survive downscaling)
  <category>/figures_ef/svg/n<NN>.svg   (crisp vector)
Reads only data/packings.json. Pure matplotlib + hand-written SVG (no pgf/tikz).
"""
import json, math, os
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle, Polygon

import os as _os; ROOT = _os.path.dirname(_os.path.abspath(__file__))
CIRINL  = os.path.join(ROOT, 'cirinl_circles_in_L')
CIRINTTT= os.path.join(ROOT, 'cirinttt_circles_in_triangles')

GRAY   = "#cccccc"
BLACK  = "#000000"
PXSIZE = 220          # target raster size (px); small so borders don't vanish when shrunk
PAD    = 0.6          # padding around the figure, in circle-radius units

def l_outline(s):
    h = s/2.0
    return [(0,0),(s,0),(s,h),(h,h),(h,s),(0,s)]

def _png(polygon, centers, path):
    xs=[p[0] for p in polygon]; ys=[p[1] for p in polygon]
    minx,maxx=min(xs)-PAD,max(xs)+PAD; miny,maxy=min(ys)-PAD,max(ys)+PAD
    W=maxx-minx; H=maxy-miny
    dpi=100
    fig=plt.figure(figsize=(PXSIZE/dpi*(W/max(W,H)), PXSIZE/dpi*(H/max(W,H))), dpi=dpi)
    ax=fig.add_axes([0,0,1,1])
    # line widths chosen to stay visible at this small size
    for (cx,cy) in centers:
        ax.add_patch(Circle((cx,cy),1.0,facecolor=GRAY,edgecolor=BLACK,linewidth=0.8))
    ax.add_patch(Polygon(polygon,closed=True,fill=False,edgecolor=BLACK,linewidth=1.1))
    ax.set_xlim(minx,maxx); ax.set_ylim(miny,maxy); ax.set_aspect('equal'); ax.axis('off')
    fig.savefig(path,dpi=dpi); plt.close(fig)

def _svg(polygon, centers, path, px=400):
    xs=[p[0] for p in polygon]; ys=[p[1] for p in polygon]
    minx,maxx=min(xs)-PAD,max(xs)+PAD; miny,maxy=min(ys)-PAD,max(ys)+PAD
    W=maxx-minx; H=maxy-miny; sc=px/max(W,H); ww,hh=W*sc,H*sc
    tx=lambda x:(x-minx)*sc; ty=lambda y:(maxy-y)*sc
    pts=" ".join(f"{tx(x):.2f},{ty(y):.2f}" for x,y in polygon)
    lw=max(1.0, sc*0.02)
    out=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{ww:.1f}" height="{hh:.1f}" viewBox="0 0 {ww:.1f} {hh:.1f}">',
         f'<rect width="{ww:.1f}" height="{hh:.1f}" fill="white"/>']
    for (cx,cy) in centers:
        out.append(f'<circle cx="{tx(cx):.2f}" cy="{ty(cy):.2f}" r="{sc:.2f}" '
                   f'fill="{GRAY}" stroke="{BLACK}" stroke-width="{lw:.2f}"/>')
    out.append(f'<polygon points="{pts}" fill="none" stroke="{BLACK}" stroke-width="{lw*1.4:.2f}"/>')
    out.append('</svg>')
    open(path,'w').write("\n".join(out))

def render(cat_dir, kind):
    packs=json.load(open(os.path.join(cat_dir,'data','packings.json')))
    pg=os.path.join(cat_dir,'figures_ef','png'); sg=os.path.join(cat_dir,'figures_ef','svg')
    os.makedirs(pg,exist_ok=True); os.makedirs(sg,exist_ok=True)
    for nk in sorted(packs,key=int):
        n=int(nk); d=packs[nk]
        if kind=='L':
            poly=l_outline(d['side_s']); P=d['centers']
        else:
            poly=[tuple(v) for v in d['triangle_vertices']]; P=d['centers']
        _png(poly,P,os.path.join(pg,f'n{n:02d}.png'))
        _svg(poly,P,os.path.join(sg,f'n{n:02d}.svg'))
    return sorted(int(k) for k in packs)

def contact_sheet(cat_dir, kind):
    """A captioned overview: each panel shows the (gray/black) packing with n and,
    for triangles, the three side lengths beneath."""
    packs=json.load(open(os.path.join(cat_dir,'data','packings.json'))); ns=sorted(packs,key=int)
    ncol=5; nrow=math.ceil(len(ns)/ncol)
    fig,axs=plt.subplots(nrow,ncol,figsize=(2.6*ncol,2.9*nrow))
    axs=axs.reshape(-1) if hasattr(axs,'reshape') else [axs]
    for ax,nk in zip(axs,ns):
        d=packs[nk]; n=int(nk)
        if kind=='L':
            poly=l_outline(d['side_s']); P=d['centers']; cap=f"$n={n}$,  $s={d['side_s']:.5f}$"
        else:
            V=d['triangle_vertices']; poly=[tuple(v) for v in V]; P=d['centers']
            s=sorted([math.dist(V[0],V[1]),math.dist(V[1],V[2]),math.dist(V[2],V[0])])
            cap=f"$n={n}$,  sides $({s[0]:.3f},\\,{s[1]:.3f},\\,{s[2]:.3f})$"
        for (cx,cy) in P:
            ax.add_patch(Circle((cx,cy),1.0,facecolor=GRAY,edgecolor=BLACK,linewidth=0.7))
        ax.add_patch(Polygon(poly,closed=True,fill=False,edgecolor=BLACK,linewidth=1.0))
        xs=[p[0] for p in poly]; ys=[p[1] for p in poly]
        ax.set_xlim(min(xs)-PAD,max(xs)+PAD); ax.set_ylim(min(ys)-PAD,max(ys)+PAD)
        ax.set_aspect('equal'); ax.axis('off'); ax.set_title(cap,fontsize=7)
    for ax in axs[len(ns):]: ax.axis('off')
    plt.tight_layout()
    fig.savefig(os.path.join(cat_dir,'figures_ef','all_packings.png'),dpi=150,bbox_inches='tight')
    plt.close(fig)

if __name__=='__main__':
    print("cirinl :", render(CIRINL,'L'));  contact_sheet(CIRINL,'L')
    print("cirinttt:", render(CIRINTTT,'tri')); contact_sheet(CIRINTTT,'tri')
    print("done")
