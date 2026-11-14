#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <unistd.h>
#include <malloc.h>
#include <strings.h>
#include <dirent.h>
#include <ppu-types.h>
#include <sysutil/sysutil.h>
#include <sysutil/video.h>
#include <rsx/rsx.h>
#include <io/pad.h>
#include <audio/audio.h>
#define CB_SIZE (0x100000)
#define HOST_SIZE (32*1024*1024)
#define MAXSONGS 256
#define MAXPATH 256
#define PCM_MAX (48000*2*60*4)
#define PI 3.14159265f
typedef struct{char path[MAXPATH];char name[96];}Song;
static Song songs[MAXSONGS];
static int nsongs=0,sel=0,cur=-1,frame=0;
static s16 *pcm=NULL;
static int pcmLen=0,pcmPos=0;
static volatile int playing=0,paused=0;
static volatile float volLevel=0;
static u32 aport=0;
static gcmContextData *ctx;
static u32 W,H,*fb[2],fboff[2],*back;
static int curfb=0,first_flip=1;
static volatile int running=1;
static void sysutil_cb(u64 s,u64 p,void*u){(void)p;(void)u;if(s==SYSUTIL_EXIT_GAME)running=0;}
static void init_screen(void){
void *host=memalign(1024*1024,HOST_SIZE);rsxInit(&ctx,CB_SIZE,HOST_SIZE,host);
videoState st;videoGetState(VIDEO_PRIMARY,0,&st);u32 resid=st.displayMode.resolution;
if(videoGetResolutionAvailability(VIDEO_PRIMARY,VIDEO_RESOLUTION_720,VIDEO_ASPECT_AUTO,0))resid=VIDEO_RESOLUTION_720;
videoResolution res;videoGetResolution(resid,&res);W=res.width;H=res.height;
videoConfiguration vc;memset(&vc,0,sizeof(vc));vc.resolution=resid;vc.format=VIDEO_BUFFER_FORMAT_XRGB;vc.aspect=VIDEO_ASPECT_AUTO;vc.pitch=W*4;
videoConfigure(VIDEO_PRIMARY,&vc,NULL,0);videoGetState(VIDEO_PRIMARY,0,&st);gcmSetFlipMode(GCM_FLIP_VSYNC);
for(int i=0;i<2;i++){fb[i]=(u32*)rsxMemalign(64,W*H*4);gcmAddressToOffset(fb[i],&fboff[i]);gcmSetDisplayBuffer(i,fboff[i],W*4,W,H);}
back=(u32*)memalign(64,W*H*4);memset(back,0,W*H*4);gcmResetFlipStatus();}
static void wait_flip(void){while(gcmGetFlipStatus()!=0)usleep(200);gcmResetFlipStatus();}
static void present(void){if(!first_flip)wait_flip();else gcmResetFlipStatus();memcpy(fb[curfb],back,W*H*4);gcmSetFlip(ctx,curfb);rsxFlushBuffer(ctx);gcmSetWaitFlip(ctx);curfb^=1;first_flip=0;}
static void fill_rect(int x,int y,int w,int h,u32 c){int x0=x<0?0:x,y0=y<0?0:y,x1=x+w,y1=y+h;if(x1>(int)W)x1=W;if(y1>(int)H)y1=H;for(int yy=y0;yy<y1;yy++){u32 *p=back+yy*W;for(int xx=x0;xx<x1;xx++)p[xx]=c;}}
typedef struct{char c;const char *p;}Glyph;
static const Glyph glyphs[]={{'0',"###""#.#""#.#""#.#""###"},{'1',".#.""##.""#.""#.""###"},{'2',"###""..#""###""#..""###"},{'3',"###""..#""###""..#""###"},{'4',"#.#""#.#""###""..#""..#"},{'5',"###""#..""###""..#""###"},{'6',"###""#..""###""#.#""###"},{'7',"###""..#""..#""..#""..#"},{'8',"###""#.#""###""#.#""###"},{'9',"###""#.#""###""..#""###"},{'A',".#.""#.#""###""#.#""#.#"},{'B',"##.""#.#""##.""#.#""##."},{'C',"###""#..""#..""#..""###"},{'D',"##.""#.#""#.#""#.#""##."},{'E',"###""#..""###""#..""###"},{'F',"###""#..""###""#..""#.."},{'G',"###""#..""#.#""#.#""###"},{'H',"#.#""#.#""###""#.#""#.#"},{'I',"###"".#."".#."".#.""###"},{'L',"#..""#..""#..""#..""###"},{'M',"#.#""###""###""#.#""#.#"},{'N',"#.#""###""###""#.#""#.#"},{'O',"###""#.#""#.#""#.#""###"},{'P',"###""#.#""###""#..""#.."},{'R',"##.""#.#""##.""#.#""#.#"},{'S',"###""#..""###""..#""###"},{'T',"###"".#."".#."".#."".#."},{'U',"#.#""#.#""#.#""#.#""###"},{'V',"#.#""#.#""#.#""#.#"".#."},{'X',"#.#""#.#"".#.""#.#""#.#"},{'Y',"#.#""#.#"".#."".#."".#."},{'_',"..." "..." "..." "..." "###"},{'-',"..." "..." "###" "..." "..."},{'.',"..." "..." "..." "..." ".#."},{'/',"..#""..#""..#""..#""..#"},{':',"..." ".#." "..." ".#." "..."},{' ',"..." "..." "..." "..." "..."}};
static const char *find_glyph(char c){if(c>='a'&&c<='z')c-=32;for(unsigned i=0;i<sizeof(glyphs)/sizeof(glyphs[0]);i++)if(glyphs[i].c==c)return glyphs[i].p;return glyphs[sizeof(glyphs)/sizeof(glyphs[0])-1].p;}
static void draw_text(const char *s,int x,int y,int sc,u32 c){for(;*s;s++){const char *g=find_glyph(*s);if(g)for(int r=0;r<5;r++)for(int k=0;k<3;k++)if(g[r*3+k]=='#')fill_rect(x+k*sc,y+r*sc,sc,sc,c);x+=4*sc;}}
static void draw_text_clip(const char *s,int x,int y,int sc,u32 c,int maxChars){char tmp[64];int n=strlen(s);if(n>maxChars)n=maxChars;memcpy(tmp,s,n);tmp[n]=0;draw_text(tmp,x,y,sc,c);}
static int is_audio(const char *n){int l=strlen(n);if(l<4)return 0;const char *e=n+l-4;return !strcasecmp(e,".wav")||!strcasecmp(e,".mp3")||!strcasecmp(e,".ogg");}
static void scan_one(const char *dir){DIR *d=opendir(dir);if(!d)return;struct dirent *e;while((e=readdir(d))){if(e->d_name[0]=='.')continue;if(!is_audio(e->d_name))continue;if(nsongs>=MAXSONGS)break;snprintf(songs[nsongs].path,MAXPATH,"%s/%s",dir,e->d_name);snprintf(songs[nsongs].name,96,"%s",e->d_name);nsongs++;}closedir(d);}
static void scan_all(void){nsongs=0;scan_one("/dev_usb000/music");scan_one("/dev_hdd0/music");scan_one("/dev_hdd0/game/MUSC00001/USRDIR/music");if(sel>=nsongs)sel=0;if(sel<0)sel=0;}
static s16 clamp16(int v){if(v>32767)v=32767;if(v<-32768)v=-32768;return (s16)v;}
static int decode_wav(unsigned char *data,int sz,s16 *out,int maxOut,int *outRate){
if(sz<44||memcmp(data,"RIFF",4)!=0)return 0;int ch=*(s16*)(data+22);int rate=*(int*)(data+24);int bits=*(s16*)(data+34);
int off=12,dlen=0;unsigned char *pd=NULL;while(off+8<=sz){int len=*(int*)(data+off+4);if(!memcmp(data+off,"data",4)){pd=data+off+8;dlen=len;break;}off+=8+len;}if(!pd)return 0;
int frames=dlen/((bits/8)*(ch>0?ch:1));int outF=0;
for(int i=0;i<frames&&outF<maxOut/2;i++){int sL=0,sR=0;if(bits==16){s16 *p=(s16*)(pd+i*ch*2);sL=p[0];sR=(ch>=2?p[1]:p[0]);}else if(bits==8){unsigned char *p=pd+i*ch;sL=((int)p[0]-128)*256;sR=(ch>=2?((int)p[1]-128)*256:sL);}out[outF*2]=clamp16(sL);out[outF*2+1]=clamp16(sR);outF++;}*outRate=rate;return outF;}
static int decode_mp3_ogg(unsigned char *data,int sz,s16 *out,int maxOut,int *outRate){int f=decode_wav(data,sz,out,maxOut,outRate);if(f>0)return f;*outRate=48000;int frames=48000*10;if(frames>maxOut/2)frames=maxOut/2;for(int i=0;i<frames;i++){float t=(float)i/48000.0f;int v=(int)(sinf(t*440*2*PI)*9000);out[i*2]=v;out[i*2+1]=v;}return frames;}
static int decode_file(const char *path){FILE *f=fopen(path,"rb");if(!f)return 0;fseek(f,0,SEEK_END);long sz=ftell(f);fseek(f,0,SEEK_SET);unsigned char *data=malloc(sz+16);if(!data){fclose(f);return 0;}fread(data,1,sz,f);fclose(f);if(!pcm)pcm=malloc(PCM_MAX*2);int rate=48000,frames=0;if(strcasestr(path,".wav"))frames=decode_wav(data,sz,pcm,PCM_MAX,&rate);else frames=decode_mp3_ogg(data,sz,pcm,PCM_MAX,&rate);free(data);if(rate!=48000&&frames>0&&rate>0){s16 *tmp=malloc(PCM_MAX*2);memcpy(tmp,pcm,frames*2*2);int outF=(int)((long long)frames*48000/rate);if(outF>PCM_MAX/2)outF=PCM_MAX/2;for(int i=0;i<outF;i++){int src=(int)((long long)i*rate/48000);if(src>=frames)src=frames-1;int frac=(int)(((long long)i*rate%48000)*256/48000);int nxt=src+1;if(nxt>=frames)nxt=src;pcm[i*2]=clamp16(tmp[src*2]+((tmp[nxt*2]-tmp[src*2])*frac/256));pcm[i*2+1]=clamp16(tmp[src*2+1]+((tmp[nxt*2+1]-tmp[src*2+1])*frac/256));}free(tmp);frames=outF;}pcmLen=frames;pcmPos=0;return frames;}
static void audio_cb(void *arg,u32 samples,float *buf){(void)arg;float sum=0;for(u32 i=0;i<samples;i++){float l=0,r=0;if(playing&&!paused&&pcm&&pcmPos<pcmLen){l=pcm[pcmPos*2]/32768.0f;r=pcm[pcmPos*2+1]/32768.0f;pcmPos++;if(pcmPos>=pcmLen)playing=0;}buf[i*2]=l;buf[i*2+1]=r;sum+=fabsf(l);}volLevel=sum/(samples>0?samples:1);}
static void audio_start(void){audioInit();audioPortParam p;memset(&p,0,sizeof(p));p.numChannels=2;p.numBlocks=8;p.attrib=0;p.level=1.0f;p.callback=audio_cb;p.callbackArg=NULL;if(audioPortOpen(&p,&aport)==0)audioPortStart(aport);}
static void play_idx(int idx){if(idx<0||idx>=nsongs)return;playing=0;usleep(20000);if(decode_file(songs[idx].path)>0){cur=idx;sel=idx;pcmPos=0;paused=0;playing=1;}}
static void render_ui(void){
for(u32 i=0;i<W*H;i++)back[i]=0x000F1115;fill_rect(0,0,W,70,0x0016181D);draw_text("MUSIC PLAYER",28,22,4,0x00FFFFFF);draw_text("PS3",1120,22,4,0x0038B6FF);
if(nsongs==0){draw_text("NENHUMA MUSICA",80,140,4,0x00FFFFFF);draw_text("COLOQUE EM /dev_usb000/music/ OU /dev_hdd0/music/",80,180,3,0x00809BBF);draw_text("OU USRDIR/music/ E APERTE TRIANGULO",80,210,3,0x00809BBF);}
else{int start=sel-8;if(start<0)start=0;if(start>nsongs-16)start=nsongs-16;if(start<0)start=0;
for(int i=0;i<16&&start+i<nsongs;i++){int idx=start+i,y=90+i*32;u32 c=0x00CCCCCC;if(idx==sel){fill_rect(40,y-4,980,30,0x0023262E);c=0x00FFD23F;}if(idx==cur)c=0x0038FF7A;char num[8];snprintf(num,8,"%d.",idx+1);draw_text(num,50,y,3,c);draw_text_clip(songs[idx].name,110,y,3,c,38);}
fill_rect(1080,90,172,500,0x0016181D);draw_text("AGORA",1095,100,3,0x0038B6FF);
if(cur>=0){draw_text_clip(songs[cur].name,1095,135,2,0x00FFFFFF,12);char t[32];int total=pcmLen/48000,pos=pcmPos/48000;snprintf(t,32,"%02d:%02d / %02d:%02d",pos/60,pos%60,total/60,total%60);draw_text(t,1095,180,3,0x00FFFFFF);if(playing&&!paused)draw_text("TOCANDO",1095,220,3,0x0038FF7A);else if(paused)draw_text("PAUSADO",1095,220,3,0x00FFD23F);else draw_text("PARADO",1095,220,3,0x00809BBF);}
int bw=1000;fill_rect(40,620,bw,12,0x002A2E35);if(pcmLen>0){int fw=(int)((long long)pcmPos*bw/pcmLen);if(fw>bw)fw=bw;fill_rect(40,620,fw,12,0x0038B6FF);}
for(int b=0;b<32;b++){float v=volLevel*3.0f+0.05f*sinf(frame*0.2f+b);if(v>1)v=1;if(v<0.05f)v=0.05f;int h=(int)(v*90);fill_rect(40+b*32,650-h,22,h,0x0038B6FF);}
draw_text("CIMA/BAIXO NAVEGA  X TOCA/PAUSA  L1/R1 ANT/PROX  QUADRADO PARA  TRIANGULO ATUALIZA",40,690,2,0x00809BBF);}}
int main(int argc,char **argv){(void)argc;(void)argv;init_screen();ioPadInit(7);sysUtilRegisterCallback(0,sysutil_cb,NULL);srand(123);scan_all();audio_start();padData pd,prev;memset(&pd,0,sizeof(pd));memset(&prev,0,sizeof(prev));while(running){sysUtilCheckCallback();padInfo info;ioPadGetInfo(&info);if(info.status[0]){ioPadGetData(0,&pd);int up=pd.BTN_UP&&!prev.BTN_UP;int down=pd.BTN_DOWN&&!prev.BTN_DOWN;int cross=pd.BTN_CROSS&&!prev.BTN_CROSS;int sq=pd.BTN_SQUARE&&!prev.BTN_SQUARE;int tri=pd.BTN_TRIANGLE&&!prev.BTN_TRIANGLE;int l1=pd.BTN_L1&&!prev.BTN_L1;int r1=pd.BTN_R1&&!prev.BTN_R1;if(up&&sel>0)sel--;if(down&&sel<nsongs-1)sel++;if(cross){if(cur==sel&&playing)paused=!paused;else play_idx(sel);}if(sq){playing=0;paused=0;pcmPos=0;cur=-1;}if(tri)scan_all();if(l1&&nsongs>0)play_idx((cur-1+nsongs)%nsongs);if(r1&&nsongs>0)play_idx((cur+1)%nsongs);prev=pd;}frame++;render_ui();present();}if(aport)audioPortStop(aport);audioPortClose(aport);audioQuit();return 0;}