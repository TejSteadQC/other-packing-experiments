#!/usr/bin/env python3
"""
Render every packing in this repository to a per-packing SVG and a high-resolution PNG.

Reads ONLY the data/packings.json files (the same coordinates the verifier checks).
Outputs, for each n:
    <category>/figures/svg/n<NN>.svg
    <category>/figures/png/n<NN>.png   (300 dpi)
plus a per-category contact-sheet PNG.

SVG is generated directly (no dependency); PNG uses matplotlib.

Usage:  python3 render.py
"""
import json, math, os

ROOT = os.path.dirname(os.path.abspath(__file__))
CIRINL = os.path.join(ROOT, 'cirinl_circles_in_L')
CIRINTTT = os.path.join(ROOT, 'cirinttt_circles_in_triangles')

# ---------------------------------------------------------------- geometry
def l_outline(s):
    """L-tromino polygon vertices (closed path)."""
    h = s/2.0
    return [(0,0),(s,0),(s,h),(h,h),(h,s),(0,s),(0,0)]

# ---------------------------------------------------------------- SVG writer
def _svg(polygon, centers, r, pad=1.0, circ_fill="#7fb3d5", circ_stroke="#1f4e79",
         poly_stroke="#000000", px=720, subtitle=""):
    xs = [p[0] for p in polygon]; ys = [p[1] for p in polygon]
    minx, maxx = min(xs)-pad, max(xs)+pad
    miny, maxy = min(ys)-pad, max(ys)+pad
    W = maxx-minx; H = maxy-miny
    scale = px / max(W, H)
    ww, hh = W*scale, H*scale
    # transform: flip y so geometry is upright; svg y grows downward
    def tx(x): return (x-minx)*scale
    def ty(y): return (maxy-y)*scale
    out = []
    out.append(f'<svg xmlns="http://www.w3.org/2000/svg" width="{ww:.1f}" height="{hh:.1f}" '
               f'viewBox="0 0 {ww:.1f} {hh:.1f}">')
    out.append(f'<rect width="{ww:.1f}" height="{hh:.1f}" fill="white"/>')
    # container
    pts = " ".join(f"{tx(x):.3f},{ty(y):.3f}" for x,y in polygon)
    out.append(f'<polygon points="{pts}" fill="none" stroke="{poly_stroke}" stroke-width="2"/>')
    # circles
    for (cx, cy) in centers:
        out.append(f'<circle cx="{tx(cx):.3f}" cy="{ty(cy):.3f}" r="{r*scale:.3f}" '
                   f'fill="{circ_fill}" fill-opacity="0.65" stroke="{circ_stroke}" stroke-width="1"/>')
        out.append(f'<circle cx="{tx(cx):.3f}" cy="{ty(cy):.3f}" r="1.4" fill="{circ_stroke}"/>')
    if subtitle:
        out.append(f'<text x="6" y="16" font-family="sans-serif" font-size="13" fill="#222">{subtitle}</text>')
    out.append('</svg>')
    return "\n".join(out)

# ---------------------------------------------------------------- PNG via mpl
def _png(polygon, centers, r, path, title, color):
    import matplotlib; matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle, Polygon
    xs=[p[0] for p in polygon]; ys=[p[1] for p in polygon]
    fig, ax = plt.subplots(figsize=(5,5))
    ax.add_patch(Polygon(polygon, closed=True, fill=False, ec='k', lw=1.8))
    for (cx,cy) in centers:
        ax.add_patch(Circle((cx,cy), r, fc=color, ec='#1f4e79' if color=='#7fb3d5' else '#7b241c',
                            alpha=0.65, lw=0.9))
        ax.plot(cx,cy,'.',ms=2,color='#1f4e79' if color=='#7fb3d5' else '#7b241c')
    ax.set_xlim(min(xs)-1, max(xs)+1); ax.set_ylim(min(ys)-1, max(ys)+1)
    ax.set_aspect('equal'); ax.axis('off'); ax.set_title(title, fontsize=12)
    fig.savefig(path, dpi=300, bbox_inches='tight'); plt.close(fig)

# ---------------------------------------------------------------- drivers
def render_cirinl():
    packs = json.load(open(os.path.join(CIRINL,'data','packings.json')))
    svgdir=os.path.join(CIRINL,'figures','svg'); pngdir=os.path.join(CIRINL,'figures','png')
    os.makedirs(svgdir,exist_ok=True); os.makedirs(pngdir,exist_ok=True)
    for nk in sorted(packs,key=int):
        n=int(nk); d=packs[nk]; s=d['side_s']; P=d['centers']
        poly=l_outline(s)
        sub=f"circles in L-tromino  n={n}  s={s:.6f}"
        open(os.path.join(svgdir,f'n{n:02d}.svg'),'w').write(_svg(poly,P,1.0,subtitle=sub))
        _png(poly,P,1.0,os.path.join(pngdir,f'n{n:02d}.png'),sub,'#7fb3d5')
    return sorted(int(k) for k in packs)

def render_cirinttt():
    packs = json.load(open(os.path.join(CIRINTTT,'data','packings.json')))
    svgdir=os.path.join(CIRINTTT,'figures','svg'); pngdir=os.path.join(CIRINTTT,'figures','png')
    os.makedirs(svgdir,exist_ok=True); os.makedirs(pngdir,exist_ok=True)
    for nk in sorted(packs,key=int):
        n=int(nk); d=packs[nk]; V=d['triangle_vertices']; P=d['centers']
        poly=[tuple(v) for v in V]+[tuple(V[0])]
        sub=f"circles in arbitrary triangle  n={n}  area={d['area']:.5f}"
        open(os.path.join(svgdir,f'n{n:02d}.svg'),'w').write(_svg(poly,P,1.0,
            circ_fill="#e8a598",circ_stroke="#7b241c",subtitle=sub))
        _png(poly,P,1.0,os.path.join(pngdir,f'n{n:02d}.png'),sub,'#e8a598')
    return sorted(int(k) for k in packs)

def contact_sheet(category_dir, packs_path, kind):
    import matplotlib; matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Circle, Polygon
    packs=json.load(open(packs_path)); ns=sorted(packs,key=int)
    ncol=5; nrow=math.ceil(len(ns)/ncol)
    fig,axs=plt.subplots(nrow,ncol,figsize=(3.4*ncol,3.4*nrow))
    axs=axs.reshape(-1) if hasattr(axs,'reshape') else [axs]
    for ax,nk in zip(axs,ns):
        d=packs[nk]; n=int(nk)
        if kind=='L':
            s=d['side_s']; poly=l_outline(s); P=d['centers']; col='#7fb3d5'; ec='#1f4e79'
            t=f"n={n}, s={s:.4f}"
        else:
            V=d['triangle_vertices']; poly=[tuple(v) for v in V]; P=d['centers']; col='#e8a598'; ec='#7b241c'
            t=f"n={n}, A={d['area']:.3f}"
        ax.add_patch(Polygon(poly,closed=True,fill=False,ec='k',lw=1.3))
        for (cx,cy) in P: ax.add_patch(Circle((cx,cy),1.0,fc=col,ec=ec,alpha=0.65,lw=0.7))
        xs=[p[0] for p in poly]; ys=[p[1] for p in poly]
        ax.set_xlim(min(xs)-1,max(xs)+1); ax.set_ylim(min(ys)-1,max(ys)+1)
        ax.set_aspect('equal'); ax.axis('off'); ax.set_title(t,fontsize=9)
    for ax in axs[len(ns):]: ax.axis('off')
    plt.tight_layout()
    fig.savefig(os.path.join(category_dir,'figures','contact_sheet.png'),dpi=150,bbox_inches='tight')
    plt.close(fig)

if __name__=='__main__':
    a=render_cirinl(); print("cirinl rendered:", a)
    contact_sheet(CIRINL, os.path.join(CIRINL,'data','packings.json'),'L')
    b=render_cirinttt(); print("cirinttt rendered:", b)
    contact_sheet(CIRINTTT, os.path.join(CIRINTTT,'data','packings.json'),'tri')
    print("done")
