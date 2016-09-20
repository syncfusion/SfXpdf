//========================================================================
//
// HtmlOutputDev.cc
//
// Copyright 1997-2002 Glyph & Cog, LLC
//
// Changed 1999-2000 by G.Ovtcharov
//
// Changed 2002 by Mikhail Kruk
//
//========================================================================

#ifdef __GNUC__
#pragma implementation
#endif
#include <vector>
#include <iostream>
#include <fstream>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stddef.h>
#include <ctype.h>
#include <math.h>
#include "GString.h"
#include "GList.h"
#include "UnicodeMap.h"
#include "gmem.h"
#include "config.h"
#include "Error.h"
#include "GfxState.h"
#include "GlobalParams.h"
#include "HtmlOutputDev.h"
#include "HtmlFonts.h"
#include "SplashOutputDev.h"
#include "SplashBitmap.h"


extern "C"
{
#include "png.h"
#include "jpeg.h"
}
#include "jpeg.c"

int HtmlPage::pgNum=0;
int HtmlOutputDev::imgNum=1;

extern double scale;
extern GBool complexMode;
extern GBool ignore;
extern GBool printCommands;
extern GBool printHtml;
extern GBool noframes;
extern GBool stout;
extern GBool xml;
extern GBool showHidden;
extern GBool noMerge;
extern GBool isContinue;
int minX=0;
int lineStringCount=0;
int previousLineYmax=0;
HtmlString *previousLineStartString;
HtmlString *stringArry[50];
bool isIntersectWithPreviousLine=false;
HtmlString *previousLine;
//std::ofstream outfile ("test.txt");
//FILE *file12=fopen("myfile.txt","w");


//FILE* pFile = fopen("logFile.txt", "w");
  
static GString* basename(GString* str){
  
  char *p=str->getCString();
  int len=str->getLength();
  for (int i=len-1;i>=0;i--)
    if (*(p+i)==SLASH) 
      return new GString((p+i+1),len-i-1);
  return new GString(str);
}

static GString* Dirname(GString* str){
  
  char *p=str->getCString();
  int len=str->getLength();
  for (int i=len-1;i>=0;i--)
    if (*(p+i)==SLASH) 
      return new GString(p,i+1);
  return new GString();
} 

//------------------------------------------------------------------------
// HtmlString
//------------------------------------------------------------------------

HtmlString::HtmlString(GfxState *state, double fontSize, double _charspace, HtmlFontAccu* fonts) {
  GfxFont *font;
  double x, y;

  state->transform(state->getCurX(), state->getCurY(), &x, &y);
  if ((font = state->getFont())) {
    yMin = y - font->getAscent() * fontSize;
    yMax = y - font->getDescent() * fontSize;
    GfxRGB rgb;
    state->getFillRGB(&rgb);
	GString *name = state->getFont()->getOrigName();
    if (!name) name = HtmlFont::getDefaultFont(); 
   // HtmlFont hfont=HtmlFont(name, static_cast<int>(fontSize-1),_charspace, rgb);
    HtmlFont hfont=HtmlFont(name, static_cast<int>(fontSize-1),0.0, rgb);
    fontpos = fonts->AddFont(hfont);
  } else {
    // this means that the PDF file draws text without a current font,
    // which should never happen
    yMin = y - 0.95 * fontSize;
    yMax = y + 0.35 * fontSize;
    fontpos=0;
  }
  if (yMin == yMax) {
    // this is a sanity check for a case that shouldn't happen -- but
    // if it does happen, we want to avoid dividing by zero later
    yMin = y;
    yMax = y + 1;
  }
  int columnNo=0;
  n=new int[50];
  multiDivLineArray=new int[50];
  col = 0;
  text = NULL;
  xRight = NULL;
  link = NULL;
  len = size = 0;
  yxNext = NULL;
  xyNext = NULL;
  strSize = 0;
  columns=0; 
  previousLineYmax=0;
  rows=0;
  marginTop=0;
  multiColumncount=0;
  lineCount=0;
  height=0;
  htext=new GString();
  htext2=new GString();
  dir = textDirUnknown;
  rightToLeft=false;
}


HtmlString::~HtmlString() {
  delete text;
  delete htext;
  delete htext2;
  /*delete [] stringArray;*/
//  delete strSize;
  gfree(xRight);
}

void HtmlString::addChar(GfxState *state, double x, double y,
			 double dx, double dy, Unicode u) {
  if (dir == textDirUnknown) {
    dir = UnicodeMap::getDirection(u);
  } 

  if (len == size) {
    size += 16;
    text = (Unicode *)grealloc(text, size * sizeof(Unicode));
    xRight = (double *)grealloc(xRight, size * sizeof(double));
  }
  text[len] = u;
  if (len == 0) {
    xMin = x;
  }
  xMax = xRight[len] = x + dx;
  //xMax = xRight[len] = x;
  ++strSize;
//printf("added char: %f %f xright = %f\n", x, dx, x+dx);
  ++len;
}

void HtmlString::endString()
{
  if( dir == textDirRightLeft && len > 1 )
  {
    //printf("will reverse!\n");
    for (int i = 0; i < len / 2; i++)
    {
      Unicode ch = text[i];
      text[i] = text[len - i - 1];
      text[len - i - 1] = ch;
    }
  }
}

//------------------------------------------------------------------------
// HtmlPage
//------------------------------------------------------------------------

HtmlPage::HtmlPage(GBool rawOrder, char *imgExtVal) {
  this->rawOrder = rawOrder;
  curStr = NULL;
  yxStrings = NULL;
  xyStrings = NULL;
  yxCur1 = yxCur2 = NULL;
  fonts=new HtmlFontAccu();
  links=new HtmlLinks();
  pageWidth=0;
  pageHeight=0;
  fontsPageMarker = 0;
  paragraphPageMarker=0;
  DocName=NULL;
  firstPage = -1;
  imgExt = new GString(imgExtVal);
  tableLineCount=0;


}

HtmlPage::~HtmlPage() {
  clear();
  if (DocName) delete DocName;
  if (fonts) delete fonts;
  if (links) delete links;
  if (imgExt) delete imgExt;  
}

void HtmlPage::updateFont(GfxState *state) {
  GfxFont *font;
  double *fm;
  char *name;
  int code;
  double w;
  
  // adjust the font size
  fontSize = state->getTransformedFontSize();
  if ((font = state->getFont()) && font->getType() == fontType3) {
    // This is a hack which makes it possible to deal with some Type 3
    // fonts.  The problem is that it's impossible to know what the
    // base coordinate system used in the font is without actually
    // rendering the font.  This code tries to guess by looking at the
    // width of the character 'm' (which breaks if the font is a
    // subset that doesn't contain 'm').
    for (code = 0; code < 256; ++code) {
      if ((name = ((Gfx8BitFont *)font)->getCharName(code)) &&
	  name[0] == 'm' && name[1] == '\0') {
	break;
      }
    }
    if (code < 256) {
      w = ((Gfx8BitFont *)font)->getWidth(code);
      if (w != 0) {
	// 600 is a generic average 'm' width -- yes, this is a hack
	fontSize *= w / 0.6;
      }
    }
    fm = font->getFontMatrix();
    if (fm[0] != 0) {
      fontSize *= fabs(fm[3] / fm[0]);
    }
  }
}

void HtmlPage::beginString(GfxState *state, GString *s) {
  curStr = new HtmlString(state, fontSize,charspace, fonts);
}


void HtmlPage::conv(){
  HtmlString *tmp;

  int linkIndex = 0;
  HtmlFont* h;
  for(tmp=yxStrings;tmp;tmp=tmp->yxNext){
     int pos=tmp->fontpos;
     //  printf("%d\n",pos);
     h=fonts->Get(pos);

     if (tmp->htext) delete tmp->htext; 
     tmp->htext=HtmlFont::simple(h,tmp->text,tmp->len);
     tmp->htext2=HtmlFont::simple(h,tmp->text,tmp->len);

     if (links->inLink(tmp->xMin,tmp->yMin,tmp->xMax,tmp->yMax, linkIndex)){
       tmp->link = links->getLink(linkIndex);
       /*GString *t=tmp->htext;
       tmp->htext=links->getLink(k)->Link(tmp->htext);
       delete t;*/
     }
  }

}


void HtmlPage::addChar(GfxState *state, double x, double y,
		       double dx, double dy, 
			double ox, double oy, Unicode *u, int uLen) {
  double x1, y1, w1, h1, dx2, dy2;
  int n, i, d;
  state->transform(x, y, &x1, &y1);
  n = curStr->len;
  d = 0;
 
  // check that new character is in the same direction as current string
  // and is not too far away from it before adding 
/*  if ((UnicodeMap::getDirection(u[0]) != curStr->dir) || 
     (n > 0 && 
      fabs(x1 - curStr->xRight[n-1]) > 0.1 * (curStr->yMax - curStr->yMin))) {
    endString();
    beginString(state, NULL);
  }*/
  state->textTransformDelta(state->getCharSpace() * state->getHorizScaling(),
			    0, &dx2, &dy2);
  dx -= dx2;
  dy -= dy2;
  state->transformDelta(dx, dy, &w1, &h1);
  if (uLen != 0) {
    w1 /= uLen;
    h1 /= uLen;
  }
/* if (d != 3)
 {
 endString();
 beginString(state, NULL);
 }
*/


  for (i = 0; i < uLen; ++i) 
  {
	if (u[i] == ' ')
        {
	    endString();
	    beginString(state, NULL);
	} else {
	    curStr->addChar(state, x1 + i*w1, y1 + i*h1, w1, h1, u[i]);
        }
   }

/*
  for (i = 0; i < uLen; ++i) {
    curStr->addChar(state, x1 + i*w1, y1 + i*h1, w1, h1, u[i]);
  }
*/
}

void HtmlPage::endString() {
  HtmlString *p1, *p2;
  double h, y1, y2;

  // throw away zero-length strings -- they don't have valid xMin/xMax
  // values, and they're useless anyway
  if (curStr->len == 0) {
    delete curStr;
    curStr = NULL;
    return;
  }

  curStr->endString();

#if 0 //~tmp
  if (curStr->yMax - curStr->yMin > 20) {
    delete curStr;
    curStr = NULL;
    return;
  }
#endif

  // insert string in y-major list
  h = curStr->yMax - curStr->yMin;
  y1 = curStr->yMin + 0.5 * h;
  y2 = curStr->yMin + 0.8 * h;
  if (rawOrder) {
    p1 = yxCur1;
    p2 = NULL;
  } else if ((!yxCur1 ||
              (y1 >= yxCur1->yMin &&
               (y2 >= yxCur1->yMax || curStr->xMax >= yxCur1->xMin))) &&
             (!yxCur2 ||
              (y1 < yxCur2->yMin ||
               (y2 < yxCur2->yMax && curStr->xMax < yxCur2->xMin)))) {
    p1 = yxCur1;
    p2 = yxCur2;
  } else {
    for (p1 = NULL, p2 = yxStrings; p2; p1 = p2, p2 = p2->yxNext) {
      if (y1 < p2->yMin || (y2 < p2->yMax && curStr->xMax < p2->xMin))
        break;
    }
    yxCur2 = p2;
  }
  yxCur1 = curStr;
  if (p1)
    p1->yxNext = curStr;
  else
    yxStrings = curStr;
  curStr->yxNext = p2;
  curStr = NULL;
}

void HtmlPage::coalesce() {
  HtmlString *str1, *str2;
  HtmlFont *hfont1, *hfont2;
  double space, horSpace, vertSpace, vertOverlap;
  GBool addSpace, addLineBreak;
  int n, i;
  double curX, curY, lastX, lastY;
  int sSize = 0;      
  double diff = 0.0;
  double pxSize = 0.0;
  double strSize = 0.0;
  double cspace = 0.0;

#if 0 //~ for debugging
  for (str1 = yxStrings; str1; str1 = str1->yxNext) {
    printf("x=%f..%f  y=%f..%f  size=%2d '",
	   str1->xMin, str1->xMax, str1->yMin, str1->yMax,
	   (int)(str1->yMax - str1->yMin));
    for (i = 0; i < str1->len; ++i) {
      fputc(str1->text[i] & 0xff, stdout);
    }
    printf("'\n");
  }
  printf("\n------------------------------------------------------------\n\n");
#endif
  str1 = yxStrings;

  if( !str1 ) return;

  //----- discard duplicated text (fake boldface, drop shadows)
  if( !complexMode )
  {
	HtmlString *str3;
	GBool found;
  	while (str1)
	{
		double size = str1->yMax - str1->yMin;
		double xLimit = str1->xMin + size * 0.2;
		found = gFalse;
		for (str2 = str1, str3 = str1->yxNext;
			str3 && str3->xMin < xLimit;
			str2 = str3, str3 = str2->yxNext)
		{
			if (str3->len == str1->len &&
				!memcmp(str3->text, str1->text, str1->len * sizeof(Unicode)) &&
				fabs(str3->yMin - str1->yMin) < size * 0.2 &&
				fabs(str3->yMax - str1->yMax) < size * 0.2 &&
				fabs(str3->xMax - str1->xMax) < size * 0.2)
			{
				found = gTrue;
				//printf("found duplicate!\n");
				break;
			}
		}
		if (found)
		{
			str2->xyNext = str3->xyNext;
			str2->yxNext = str3->yxNext;
			delete str3;
		}
		else
		{
			str1 = str1->yxNext;
		}
	}		
  }
  
  str1 = yxStrings;
  
  hfont1 = getFont(str1);

  str1->htext2->append(str1->htext);
  if( str1->getLink() != NULL ) {
    GString *ls = str1->getLink()->getLinkStart();
    str1->htext->insert(0, ls);
    delete ls;
  }
  curX = str1->xMin; curY = str1->yMin;
  lastX = str1->xMin; lastY = str1->yMin;

  while (str1 && (str2 = str1->yxNext)) {
    hfont2 = getFont(str2);
    space = str1->yMax - str1->yMin;
    horSpace = str2->xMin - str1->xMax;
    addLineBreak = !noMerge && (fabs(str1->xMin - str2->xMin) < 0.4);
    vertSpace = str2->yMin - str1->yMax;

//printf("coalesce %d %d %f? ", str1->dir, str2->dir, d);

    if (str2->yMin >= str1->yMin && str2->yMin <= str1->yMax)
    {
	vertOverlap = str1->yMax - str2->yMin;
    } else
    if (str2->yMax >= str1->yMin && str2->yMax <= str1->yMax)
    {
	vertOverlap = str2->yMax - str1->yMin;
    } else
    {
    	vertOverlap = 0;
    } 
    
    if (
	(
	 (
	  (
	   (rawOrder && vertOverlap > 0.5 * space) 
	   ||
	   (!rawOrder && str2->yMin < str1->yMax)
	  ) &&
	  (horSpace > -0.5 * space && horSpace < space)
	 ) ||
       	 (vertSpace >= 0 && vertSpace < 0.5 * space && addLineBreak)
	) &&
 // in complex mode fonts must be the same, in other modes fonts do not metter
	str1->dir == str2->dir // text direction the same
       ) 
    {
     diff = str2->xMax - str1->xMin;

     n = str1->len + str2->len;
     if ((addSpace = horSpace > 0.1 * space)) {
        ++n;
      }
    
      if (addLineBreak) {
        ++n;
      }
  
      str1->size = (n + 15) & ~15;
      str1->text = (Unicode *)grealloc(str1->text,
				       str1->size * sizeof(Unicode));
      str1->xRight = (double *)grealloc(str1->xRight,
					str1->size * sizeof(double));
      if (addSpace) {
		/*  if (addSpace > (xoutRoundLower(hfont1->getSize()/scale)))
		  {
		  	str1->text[str1->len] = 0x20;
			str1->htext->append(" ");
			str1->htext2->append(" ");
			str1->xRight[str1->len] = str2->xMin;
			++str1->len;
			++str1->strSize;
		 } */
  	   	 str1->text[str1->len] = 0x20;
                 str1->htext->append(" ");
                 str1->htext2->append(" ");
                 str1->xRight[str1->len] = str2->xMin;
                 ++str1->len;
                ++str1->strSize;
      }
      if (addLineBreak) {
	  str1->text[str1->len] = '\n';
	  str1->htext->append("<br>");
	  str1->htext2->append(" ");
	  str1->xRight[str1->len] = str2->xMin;
	  ++str1->len;
	  str1->yMin = str2->yMin;
	  str1->yMax = str2->yMax;
	  str1->xMax = str2->xMax;
	  int fontLineSize = hfont1->getLineSize();
	  int curLineSize = (int)(vertSpace + space); 

	  if( curLineSize != fontLineSize )
	  {
	      HtmlFont *newfnt = new HtmlFont(*hfont1);
	      newfnt->setLineSize(curLineSize);
	      str1->fontpos = fonts->AddFont(*newfnt);
	      delete newfnt;
	      hfont1 = getFont(str1);
	      // we have to reget hfont2 because it's location could have
	      // changed on resize  GStri;ng *iStr=GString::fromInt(i);
	      hfont2 = getFont(str2); 
	  }

      }
      str1->htext2->append(str2->htext2);

      HtmlLink *hlink1 = str1->getLink();
      HtmlLink *hlink2 = str2->getLink();

      GString *fntFix;
      GString *iStr=GString::fromInt(str2->fontpos);     
      fntFix = new GString("</span><span class=\"ft");
      fntFix->append(iStr);
      fntFix->append("\">");
      if (((hlink1 == NULL) && (hlink2 == NULL)) && (hfont1->isEqualIgnoreBold(*hfont2) == gFalse))
      {
	str1->htext->append(fntFix);
      }
      for (i = 0; i < str2->len; ++i) {
	str1->text[str1->len] = str2->text[i];
	str1->xRight[str1->len] = str2->xRight[i];
	++str1->len;
      }

      if( !hlink1 || !hlink2 || !hlink1->isEqualDest(*hlink2) ) {
	if(hlink1 != NULL )
	  str1->htext->append("</a>");
	if(hlink2 != NULL ) {
	  GString *ls = hlink2->getLinkStart();
	  str1->htext->append(ls);
	  delete ls;
	}
      }

      str1->htext->append(str2->htext);
      sSize = str1->htext2->getLength();      
      pxSize = xoutRoundLower(hfont1->getSize()/scale);
      strSize = (pxSize*(sSize-2));   
      cspace = (diff / strSize);//(strSize-pxSize));
     // we check if the fonts are the same and create a new font to ajust the text
//      double diff = str2->xMin - str1->xMin;
//      printf("%s\n",str1->htext2->getCString());
      // str1 now contains href for link of str2 (if it is defined)
      str1->link = str2->link; 

      HtmlFont *newfnt = new HtmlFont(*hfont1);
      newfnt->setCharSpace(cspace);
      //newfnt->setLineSize(curLineSize);
      str1->fontpos = fonts->AddFont(*newfnt);
      delete newfnt;
      hfont1 = getFont(str1);
      // we have to reget hfont2 because it's location could have
      // changed on resize  GStri;ng *iStr=GString::fromInt(i);
      hfont2 = getFont(str2); 

      hfont1 = hfont2;

      if (str2->xMax > str1->xMax) {
	str1->xMax = str2->xMax;
      }

      if (str2->yMax > str1->yMax) {
	str1->yMax = str2->yMax;
      }

      str1->yxNext = str2->yxNext;

      delete str2;
    } else { 

//     printf("startX = %f, endX = %f, diff = %f, fontsize = %d, pxSize = %f, stringSize = %d, cspace = %f, strSize = %f\n",str1->xMin,str1->xMax,diff,hfont1->getSize(),pxSize,sSize,cspace,strSize);

// keep strings separate
//      printf("no\n"); 
//      if( hfont1->isBold() )
      if(str1->getLink() != NULL )
	str1->htext->append("</a>");  
     
      str1->xMin = curX; str1->yMin = curY; 
      str1 = str2;
      curX = str1->xMin; curY = str1->yMin;
      hfont1 = hfont2;

      if( str1->getLink() != NULL ) {
	GString *ls = str1->getLink()->getLinkStart();
	str1->htext->insert(0, ls);
	delete ls;
      }
    }
  }
  str1->xMin = curX; str1->yMin = curY;

  if(str1->getLink() != NULL )
    str1->htext->append("</a>");

#if 0 //~ for debugging
  for (str1 = yxStrings; str1; str1 = str1->yxNext) {
    printf("x=%3d..%3d  y=%3d..%3d  size=%2d ",
	   (int)str1->xMin, (int)str1->xMax, (int)str1->yMin, (int)str1->yMax,
	   (int)(str1->yMax - str1->yMin));
    printf("'%s'\n", str1->htext->getCString());  
  }
  printf("\n------------------------------------------------------------\n\n");
#endif

}


void HtmlPage::dumpAsXML(FILE* f,int page){  
  fprintf(f, "<page number=\"%d\" position=\"absolute\"", page);
  fprintf(f," top=\"0\" left=\"0\" height=\"%d\" width=\"%d\">\n", pageHeight,pageWidth);
    
  for(int i=fontsPageMarker;i < fonts->size();i++) {
    GString *fontCSStyle = fonts->CSStyle(i);
    fprintf(f,"\t%s\n",fontCSStyle->getCString());
    delete fontCSStyle;
  }
  
  GString *str, *str1;
  for(HtmlString *tmp=yxStrings;tmp;tmp=tmp->yxNext){
    if (tmp->htext){
      str=new GString(tmp->htext);
      fprintf(f,"<text top=\"%d\" left=\"%d\" ",xoutRound(tmp->yMin),xoutRound(tmp->xMin));
      fprintf(f,"width=\"%d\" height=\"%d\" ",xoutRound(tmp->xMax-tmp->xMin),xoutRound(tmp->yMax-tmp->yMin));
      fprintf(f,"font=\"%d\">", tmp->fontpos);
      if (tmp->fontpos!=-1){
		  str1=fonts->getCSStyle(tmp->fontpos, str);
      }
      fputs(str1->getCString(),f);
      delete str;
      delete str1;
      fputs("</text>\n",f);
    }
  }
  fputs("</page>\n",f);
}


void HtmlPage::dumpComplex(FILE *file, int page)
{	
  FILE* pageFile;
  GString* tmp;
  char* htmlEncoding;
  int tempLocalcount=0; 
  previousLineYmax=0;
  isMultiColumn=false;
  lineWidth=0;
  lineYMax=0,lineYMin=0;
 
  if( firstPage == -1 ) firstPage = page; 
  
  if( !noframes )
  {
      GString* pgNum=GString::fromInt(page);
      tmp = new GString(DocName);
      tmp->append('-')->append(pgNum)->append(".html");
      delete pgNum;
  
      if (!(pageFile = fopen(tmp->getCString(), "w"))) 
	  {
		  error(-1, "Couldn't open html file '%s'", tmp->getCString());
		  delete tmp;
		  return;
	  } 
      delete tmp;

      fprintf(pageFile,"%s\n<html>\n<head>\n<title>Page %d</title>\n\n",
	      DOCTYPE, page);

      htmlEncoding = HtmlOutputDev::mapEncodingToHtml
	  (globalParams->getTextEncodingName());
      fprintf(pageFile, "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=%s\">\n", htmlEncoding);
  }
  else 
  {
      pageFile = file;
      fprintf(pageFile,"<!-- Page %d -->\n", page);
      fprintf(pageFile,"<a name=\"%d\"></a>\n", page);
  }   
  fprintf(pageFile,"<div class=\"bcimg%d\" style=\"position:relative;width:%d;height:%d;\">\n",(page-firstPage+1), pageWidth, pageHeight);
  if(!complexMode)
  { 
	  fprintf(pageFile,"<div class=\"bcimg%d\" style=\"position:absolute;width:%d;height:%d;\">\n",(page-firstPage+1), pageWidth, pageHeight);
  }
  tmp=basename(DocName);
   
  fputs("<style type=\"text/css\">\n<!--\n",pageFile);
  for(int i=fontsPageMarker;i!=fonts->size();i++) 
  {
    GString *fontCSStyle = fonts->CSStyle(i);
    fprintf(pageFile,"\t%s\n",fontCSStyle->getCString());
    delete fontCSStyle;
  }
  if(!complexMode)
  {
	  fprintf(pageFile,"\t.bcimg%d{background-image: url(\"%s%03d.%s\");\n",(page-firstPage+1),tmp->getCString(), (page-firstPage+1), imgExt->getCString());
	  fprintf(pageFile,"\tbackground-repeat: no-repeat;}");
  }
  GString *str, *str1;
  int yValue=0;
  HtmlString *previousLine;
  if(yxStrings!=NULL)
  yValue=xoutRound(yxStrings->yMin);
  bool isbegin=false;
  bool isTable=false; 
  int MaxColumn=0;
  int previousColumncount=0,previousColumnXvalue=0,lineStartColumnYvalue=0;
  int xValues[20];
  int yValues[50];
  int x=0,y=0,temp=0;
  int xIncrement=0,yIncrement=0; 
  int tempx=0;
  int previousColumnNO=0;
  int marginTop=yValue; 
  bool isEndofPage=false;
  bool isNewLine=false;
 
 
  HtmlString *tempstring,*temp1string; 
  int count=0;
  int m=0;
  if(!complexMode)
	  {
  for(HtmlString *tmp1=yxStrings;tmp1;tmp1=tmp1->yxNext){	 
	  m++;
	 if(m==30)
	 {
		 bool b=true;
	 }
    if (tmp1->htext){			
      str=new GString(tmp1->htext);	  	
	  tmp1->height=xoutRound(tmp1->yMax)-xoutRound(tmp1->yMin);
	  HtmlFont *font=getFont(tmp1);
	  if(isbegin)
	  {
	   if(yValue>tmp1->yMin)
	   {
		    isNewLine=false;
			marginTop=xoutRound(yValue-tmp1->yMin);
	   }
	   else
	   {
		   isNewLine=true;
		   marginTop= xoutRound(tmp1->yMin)-yValue;
	   }
	   if(previousLineYmax>tmp1->yMin)
	   {		  
		   HtmlFont *font= getFont(tmp1);
		   int a=previousLineYmax-xoutRound(tmp1->yMin);
		   if(a>3||font->size+a>xoutRound(tmp1->yMax)-xoutRound(tmp1->yMin))
		   {
			    isIntersectWithPreviousLine=true;
		   }		 
	   }
	  }
	
	  if(!complexMode)
	  {
	    if (tmp1->fontpos!=-1){
			  str1=fonts->getCSStyle(tmp1->fontpos, str,tmp1->paragraphStyle);  
		  }			
		
		  fprintf(pageFile,"\t.p%d{text-align:left;padding-left: %dpx;margin-top: %dpx;margin-bottom: 0px;}\n",paragraphPageMarker,xoutRound(tmp1->xMin),yValue,xoutRound(tmp1->yMax-tmp1->yMin));				
		  tmp1->marginTop=marginTop;
		  tmp1->columns=0;
		  tmp1->tagEnd=false;
		  tmp1->tagStart=false;
		  tmp1->rightToLeft=false;
		  tmp1->isInterSect=false;
		  tmp1->isMultiColumnTable=false;
		  tmp1->isEndLine=false;	
		  tmp1->previousLineYmax=0;		  
		  tmp1->isFirst=false;
		  tmp1->isPreviousLine=true;

		  if(!isTable&&lineStartColumnYvalue>0)
		  {
			  bool isPresent=false;		
			  bool isTextPresent=false;
			 if(count>0)
			 {
				isPresent= CheckIsPresent(xValues,xIncrement,xoutRound(tempstring->xMin));
				isTextPresent=	CheckWhetherTextIsPresent(stringArry,count,tempstring);
				if(!isPresent)
				{
					xValues[xIncrement]=xoutRound(tempstring->xMin);
					xIncrement++;
				}
				if(!isTextPresent)
				{
					stringArry[count]=tempstring;
					count++;
				}
			 }
			 else
			 {
				 xValues[xIncrement]=xoutRound(tempstring->xMin);
				 xIncrement++;
				 stringArry[count]=tempstring;
				 count++;
			 }
		  }
	  }
	 
	  tmp1->paragraphStyle=paragraphPageMarker;
	  paragraphPageMarker++;	
	  isbegin=true;	
	  if(yValue<xoutRound(tmp1->yMax))
	  {
		  yValue=xoutRound(tmp1->yMax);		
	  }
	  if(isNewLine)
	  {
		  if(lineStartColumnYvalue<xoutRound(tmp1->yMax)&&xIncrement>0)
		  {
			  if(isIntersectWithPreviousLine)
			  {
				  HtmlString *s[30];
				  int temp=0;
				  int n=previousLine->multiColumncount;
				  for(int j=0;j<n;j++)
				  {
					  bool isPresent=false;
					  for(int k=0;k<xIncrement;k++)
					  {
						  if(xValues[k]==xoutRound(previousLine->stringArray[j]->xMin))
						  {
							  isPresent=true;
						  }
					  }
					  if(!isPresent)
					  {
						  xValues[xIncrement]=xoutRound(previousLine->stringArray[j]->xMin);
						  xIncrement++;
					  }
				  }
				  for(int i=0;i<n;i++)
				  {
					  s[temp]=previousLine->stringArray[i];
					  temp++;
				  }
				  for(int i=0;i<count;i++)
				  {
					  s[temp]=stringArry[i];
					  temp++; 
				  }
				  previousLineYmax=previousLine->previousLineYmax;
				  tempstring=previousLine;
				  tempstring =SeparateColumn(tempstring,xValues,xIncrement,s,temp);				  
			  }
			  else
			  {
				  tempstring =SeparateColumn(tempstring,xValues,xIncrement,stringArry,count); 
			  }			  
			 
			  if(previousLineYmax>0&&!isIntersectWithPreviousLine)
				   tempstring->previousLineYmax=previousLineYmax;	
			  else if(previousLineYmax==0)
				  tempstring->previousLineYmax=0;
			  previousLineYmax= GetMaximumY(stringArry,count);		//xoutRound(stringArry[count-1]->yMax);
			  previousLine=tempstring;  
			  tempstring=tmp1;
			  count=0;
			  xIncrement=0;
			  isIntersectWithPreviousLine=false;
		  }
	  } 
	  else
	  {		  	  
		  tempstring=tmp1;
	  }
	  if(lineStartColumnYvalue<tmp1->yMax)
		  lineStartColumnYvalue=xoutRound(tmp1->yMax);	
	  if(tmp1->yxNext==NULL)
	  {
		  bool isPresent= CheckIsPresent(xValues,xIncrement,xoutRound(tempstring->xMin));
		  bool	isTextPresent=	CheckWhetherTextIsPresent(stringArry,count,tempstring);
		  if(!isPresent)
		  {
			  xValues[xIncrement]=xoutRound(tempstring->xMin);
			  xIncrement++;
		  }
		  if(!isTextPresent)
		  {
			  stringArry[count]=tempstring;
			  count++;
		  }
		  tempstring =SeparateColumn(tempstring,xValues,xIncrement,stringArry,count);
		  previousLine=tempstring;
		  tempstring=tmp1;
		  count=0;
		  xIncrement=0;


				 /* if(!isEndofPage)
				  {
					  if(!CheckIsPresent(xValues,xIncrement,xoutRound(tmp1->xMin)))
					  {
						  xValues[xIncrement]=xoutRound(tmp1->xMin);					 
						  xIncrement++;					 
					  }
					  bool isTextPresent=false;
					  for(int i=0;i<count;i++)
					  {
						  if(stringArry[i]->htext==tmp1->htext)
						  {
							  isTextPresent=true;					  
						  }
					  }
					  if(!isTextPresent)
					  {
						  stringArry[count]=tmp1;
						  count++;
					  }

					  previousLineStartString=tempstring;
					 tempstring =SeparateDiv(tempstring,xValues,xIncrement,stringArry,count);	
					  xIncrement=0;
					  isTable=false;	
					  count=0;	
				  }
			*/  }
		   
	  if(lineStartColumnYvalue<xoutRound(tmp1->yMax))
	  {
		  lineStartColumnYvalue=xoutRound(tmp1->yMax);
		 
	  }	
		 }
	  
	}	
  }  	

  total=xIncrement;
  fputs("-->\n</style>\n",pageFile);
  
  if( !noframes )
  {  
      fputs("</head>\n<body bgcolor=\"#FFFFFF\" vlink=\"blue\" link=\"blue\">\n",pageFile); 
  }
  
  if(complexMode)
  {  
	  if( !ignore ) 
	  {
		  fprintf(pageFile,"<img width=\"%d\" height=\"%d\" src=\"%s%03d.%s\" alt=\"background image\">\n",  pageWidth, pageHeight, tmp->getCString(), (page-firstPage+1), imgExt->getCString());
	  }
  }  
  delete tmp;
     m=0;
  for(HtmlString *tmp1=yxStrings;tmp1;tmp1=tmp1->yxNext){
	  m++;
	  if(m==59)
	  {
	  bool b=true;
	  }
    if (tmp1->htext){
      str=new GString(tmp1->htext);
	  if(complexMode)
	  {
		  fprintf(pageFile,"<div style=\"position:absolute;top:%d;left:%d\">", xoutRound(tmp1->yMin), xoutRound(tmp1->xMin));
		  fputs("<nobr>",pageFile); 

		  if (tmp1->fontpos!=-1){
			  str1=fonts->getCSStyle(tmp1->fontpos, str);  
      }    
      fputs(str1->getCString(),pageFile);
      
      delete str;      
      delete str1;
      fputs("</nobr></div>\n",pageFile);
	  }
	  else
	  {  
		  if (tmp1->fontpos!=-1)
		  {
			  if(tmp1->columns>0)
			  {						
				  if(tmp1->rows>0)
					  tmp1=DrawTable(pageFile,page,tmp1);
				  else
				  {								  					
					  tmp1=DrawMultiColumnTables(pageFile,page,tmp1);
				  }
				  if(!isMultiColumn)
					  isMultiColumn=true;
			  }			
			  else
			  {
				  if(isMultiColumn)
				  {
					  str1=fonts->getCSStyle(tmp1->fontpos, str,tmp1->paragraphStyle,true,tmp1->marginTop,tmp1->xMax);  		
				  }
				  else				  
				  str1=fonts->getCSStyle(tmp1->fontpos, str,tmp1->paragraphStyle);  
				  fputs(str1->getCString(),pageFile);
				  previousLineYmax=tmp1->yMax;
				  delete str1; 
			  }			   		  
		  }		 
		  delete str;  
		   if(tmp1==NULL)
			   break;
	  }
    }
  }
  	
  //outfile.close();

 
  fputs("</div>\n", pageFile);
  if(!complexMode)
	   fputs("</div>\n", pageFile);
  

  if( !noframes )
  {
      fputs("</body>\n</html>\n",pageFile);
      fclose(pageFile);
  }
}

HtmlString* HtmlPage::GetMaxY(HtmlString *str,int count)
{
	HtmlString *MaxString;
	int yMax=0;
	for(int i=0;i<count;i++)
	{
		if(yMax<xoutRound(str->stringArray[i]->yMax))
		{
			yMax=xoutRound(str->stringArray[i]->yMax);
			MaxString=str->stringArray[i];
		}
	}
	return MaxString;
}

int HtmlPage:: GetMinY(HtmlString *str1,int count)
{
	int Ymin=xoutRound(str1->stringArray[0]->yMin);

	for(int i=0;i<count;i++)
	{
		Ymin>xoutRound(str1->stringArray[i]->yMin);
	}
	return Ymin;
}
int HtmlPage::GetMaximumY(HtmlString *str1[],int count)
{
	int yMax=0;
	for(int i=0;i<count;i++)
	{
		if(str1[i]->yMax>yMax)
		{
			yMax=xoutRound(str1[i]->yMax);
		}
	}
	return yMax;
}

 bool HtmlPage::ChecktheStringIsSameLine(int *xValue,int count,HtmlString *str1[],int length)
 {
	 int temp=0;
	 bool isSameLine=true;
	 HtmlString *s=str1[0];
		for(int i=0;i<count;i++)
		{
			for(int j=0;j<count;j++)
			{
				if(xValue[i]<xValue[j])
				{
					temp=xValue[i];
					xValue[i]=xValue[j];
					xValue[j]=temp;
				}
			}
		}
		temp=0;
		for(int i=0;i<length;i++)
		{
			for(int k=0;k<length;k++)
			{
				if(xValue[i]==xoutRound(str1[k]->xMin))
				{
					s->stringArray[temp]=str1[k];
					temp++; 
				}
			}
			s->multiDivLineArray[i]=temp;
		}
		for(int i=0;i<count;i++)
		{
			if(i==1)
				s->n[0]=xValue[i];
			else if(i>1)
			{
				int t=0;
				for(int j=0;j<i-1;j++)
				{
					t+=s->n[j];
				}
				s->n[i-1]=xValue[i]-t;
				if(i==count-1)
					s->n[i]=pageWidth-t;
			}
		}

		int start=0;
		int end=0;
		for(int i=0;i<count;i++)
		{
		
		if(i==0)
		{
			start=0;
			end=s->multiDivLineArray[i];
		}
		else
		{
			start=end;
			end=s->multiDivLineArray[i];
		}
		for(int j=start;j<end;j++)
		{
			if(j==0)
			{
				if(s->n[i]<xoutRound(s->stringArray[j]->xMax))
				{
					if(s->n[i]+s->n[i+1]>=xoutRound(s->stringArray[j]->xMax))
					{
						isSameLine=false;
					}
				}
			}
			else
			{
				if(s->n[i]<xoutRound(s->stringArray[j]->xMax-s->stringArray[j]->xMin))
				{	
					if(s->n[i]+s->n[i+1]>=xoutRound(s->stringArray[j]->xMax-s->stringArray[j]->xMin))
					{
						isSameLine=false;					
					}
				}
			}
		}
	}
		return isSameLine;
 }

//Separate MultiColumn text.
HtmlString* HtmlPage::SeparateColumn(HtmlString *string,int *xArray,int count,HtmlString *strArr[],int length)
{	
	int startingLineYmax=xoutRound(strArr[0]->yMax);
	int xmax=xoutRound(strArr[0]->xMax);
	int i=0;
	bool isSameLine=false;
	HtmlString *s;
	if(isIntersectWithPreviousLine)
		s=string;
	else
		s=strArr[0];
	s->multiColumncount=length;
	//Detect First Line.
	for( i=1;i<length;i++)
	{
		if(xmax>xoutRound(strArr[i]->xMin))
		{
			break;
		}
	}	
	if(i==1&&count==2)
	{
		s=UpdateTopMargins(string,xArray,count,strArr,length);
		return s;
	}
		//s=UpdateTopMargins(xArray,count,strArr,length);
	//isSameLine=ChecktheStringIsSameLine(xArray,count,strArr,length);

	if(i==length&&count==length)
	{
		int temp=0;
		for(int i=0;i<count;i++)
		{
			for(int j=0;j<count;j++)
			{
				if(xArray[i]<xArray[j])
				{
					temp=xArray[i];
					xArray[i]=xArray[j];
					xArray[j]=temp;
				}
			}
		}
		int Total=0;
		for(int j=0;j<length;j++)
		{
			for(int k=0;k<length;k++)
			{
				if(xArray[j]==xoutRound(strArr[k]->xMin))
					s->stringArray[j]=strArr[k];
			}			
			if(previousLineYmax>0)
			{
				s->stringArray[j]->marginTop=xoutRound(s->stringArray[j]->yMin)-previousLineYmax;
			}
			else
			{
				s->stringArray[j]->marginTop=xoutRound(s->stringArray[j]->yMin);
			}			
			s->multiDivLineArray[j]=j+1;
			if(j>0)
			{
				s->n[j-1]=xoutRound(xArray[j])-Total;
				Total+=s->n[j-1];
				if(j!=length-1&&s->n[j-1]<(xoutRound(s->stringArray[j]->xMax)-xoutRound(s->stringArray[j]->xMin)))
				{
					s=UpdateTopMargins(string,xArray,count,strArr,length);
					return s;
				}
			}
		}
		s->n[length-1]=pageWidth-Total;
		s->columns=length;
		s->lastLine=strArr[length-1];
	}
	else
	{
		s=SeparateColumns(s,i,xArray,count,strArr,length);
		
		
	}
	return s;
}

HtmlString* HtmlPage::SeparateColumns(HtmlString *string,int firstLineColumn,int *xArray,int count,HtmlString *strArr[],int length)
{
	HtmlString *s;
	if(isIntersectWithPreviousLine)
		s=string;
	else
		s=strArr[0];
	int firstLineNoofColumn=firstLineColumn>count?count:firstLineColumn;
	if(count==2&&firstLineColumn==1)
		firstLineColumn=2;
	int i=firstLineColumn;
	int *firstLineXArray=new int[firstLineNoofColumn];

		if(i>count)
			i=count;

		//Get the First Line XminArray.
		for(int j=0;j<firstLineNoofColumn;j++)
		{
			firstLineXArray[j]=xoutRound(strArr[j]->xMin);
			strArr[j]->columnNo=j;
		}

		bool isXminLineisMissing=false;
		//Compare the Other Lines string Xmin with First line XminArray.
		for(i;i<length;i++)
		{
			bool isNotpresent=true;
			for(int j=0;j<firstLineNoofColumn;j++)
			{
				if(firstLineXArray[j]==xoutRound(strArr[i]->xMin))
				{
					strArr[i]->columnNo=j;
					isNotpresent=false;
					break;
				}				
			}
			if(isNotpresent)
			{
				bool isGreater=true;
				for(int k=0;k<firstLineNoofColumn;k++)
				{ 					
					if(xoutRound(strArr[i]->xMin)<firstLineXArray[k])
					{
						isGreater=false;
					}
				}
				if(!isGreater)
				isXminLineisMissing=true; 
				else
					strArr[i]->columnNo=firstLineNoofColumn-1;
			}
		}
		if(isXminLineisMissing)
		{
			s=UpdateTopMargins(string,xArray,count,strArr,length);
		}
		else
		{
			int temp=0;
			int start=0,end=0;
			int TotalColumnWidth=0;
			int Xmin=0;
			for(int i=0;i<firstLineNoofColumn;i++)
			{
				TotalColumnWidth=0;
				start=temp;		
				if(i>0)
					Xmin=xoutRound(strArr[i]->xMin);
				int columnNo=strArr[i]->columnNo;
				for(int j=0;j<length;j++)
				{
					if(columnNo==strArr[j]->columnNo)
					{
						if(Xmin>xoutRound(strArr[j]->xMin))
						{
							Xmin=xoutRound(strArr[j]->xMin);
						}
						s->stringArray[temp]=strArr[j];
						temp++;
					}
				}
				end=temp;		
				if(i>1)
				{
					for(int k=0;k<i-1;k++)			  
					{
						TotalColumnWidth+= s->n[k];
					}
					s->n[i-1]=xArray[i]-TotalColumnWidth;					
				}
				else if(i==1)
					s->n[i-1]=Xmin;
				s->multiDivLineArray[i]=temp;
				s->multiColumncount=length;
				SetTopMargins(s,start,end);
			}
			TotalColumnWidth=0;
			for(int k=0;k<firstLineNoofColumn-1;k++)			  
			{
				TotalColumnWidth+= s->n[k];
			}
			s->n[firstLineNoofColumn-1]=pageWidth-TotalColumnWidth;
			s->lastLine=strArr[length-1];
			s->columns=firstLineNoofColumn;
			bool isIntersect=false;
			for(int i=0;i<firstLineNoofColumn;i++)
			{
				if(i==0)
				{
					start=0;
					end=s->multiDivLineArray[i];
				}
				else
				{
					start=end;
					end=s->multiDivLineArray[i];
				}
				for(int j=start;j<end;j++)
				{
					if(j==0)
					{
						if(s->n[i]<xoutRound(s->stringArray[j]->xMax))
						{
							isIntersect=true;
						}
					}
					else
					{
						if(s->n[i]<xoutRound(s->stringArray[j]->xMax-s->stringArray[j]->xMin))
						{
							isIntersect=true;
						}
					}
				} 
			}
			//if(firstLineNoofColumn==1)
			//{
			//	for(int i=0;i<count;i++)
			//	{
			//		for(int j=0;j<count;j++)
			//		{
			//			if(xArray[i]<xArray[j])
			//			{
			//				temp=xArray[i];
			//				xArray[i]=xArray[j];
			//				xArray[j]=temp;
			//			}
			//		}
			//	}
			//	HtmlString *s1,*s2;
			//	temp=0;
			//	for(int i=0;i<count;i++)
			//	{ 
			//		
			//		int x=xArray[i];
			//		for(int j=0;j<length;j++)
			//		{
			//			if(x==xoutRound(s->stringArray[j]->xMin))
			//			{
			//				s1=s->stringArray[j];
			//				s2=s->stringArray[temp];
			//				if(j!=temp)
			//				{
			//					s->stringArray[temp]=s1;
			//					s->stringArray[j]=s2;
			//				}
			//				temp++;
			//			}
			//		}
			//	}

			//	//s=UpdateTopMargins(string,xArray,count,strArr,length);
			//}
			//previousLineYmax=xoutRound(s->lastLine->yMax);
		}
		return s;
}


HtmlString* HtmlPage::SetTopMargins(HtmlString *tmp1,int startingPoint,int count)
{
	int Ymax=xoutRound(tmp1->stringArray[startingPoint]->yMax);
	if(previousLineYmax==0)
	{
		tmp1->stringArray[startingPoint]->marginTop=xoutRound(tmp1->stringArray[startingPoint]->yMin);
	}
	else
	{
		tmp1->stringArray[startingPoint]->marginTop=xoutRound(tmp1->stringArray[startingPoint]->yMin)-previousLineYmax;
	}
	for(int i=startingPoint+1;i<count;i++)
	{
		HtmlFont *font=getFont(tmp1->stringArray[i]);
		tmp1->stringArray[i]->marginTop=xoutRound(tmp1->stringArray[i]->yMin)-Ymax;
		if(tmp1->stringArray[i]->marginTop<0)
		{
			tmp1->stringArray[i]->marginTop=tmp1->stringArray[i]->yMin-Ymax;
		}
		Ymax=xoutRound(tmp1->stringArray[i]->yMax);
	}
	return tmp1;
}


HtmlString *HtmlPage::UpdateTopMargins( HtmlString *string,int *xValue,int count,HtmlString *str1[],int length)
{
	int temp=0;
	int start=0;
	int end=0;int TotalColumnWidth=0;
	HtmlString *s;
	if(isIntersectWithPreviousLine)
		s=string;
	else
		s=str1[0];	
	int c=0;
	int *interserctColumnArray=new int[count];
	for(int i=0;i<count;i++)
    {
        for(int j=0;j<count;j++)
        {
            if(xValue[i]<xValue[j])
            {
                temp=xValue[i];
                xValue[i]=xValue[j];
                xValue[j]=temp;
            }
        }
    }
	
	for(int i=0;i<count;i++)
	{
		TotalColumnWidth=0;
		if(i>1)
		{
			for(int k=0;k<i-1;k++)			  
			{
				TotalColumnWidth+= s->n[k];
			}
			s->n[i-1]=xValue[i]-TotalColumnWidth;
		}
		else if(i==1)
			s->n[i-1]=xValue[i];;
	}
	TotalColumnWidth=0;
	for(int k=0;k<count-1;k++)			  
	{
		TotalColumnWidth+= s->n[k];
	}
	s->n[count-1]=pageWidth-TotalColumnWidth;

	temp=0;
	for(int j=0;j<count;j++)
	{ 
		int Xmin=xValue[j];
		for(int k=0;k<length;k++)
		{
			if(Xmin==xoutRound(str1[k]->xMin))
			{
				s->stringArray[temp]=str1[k];
				temp++;
			}
		}
		s->multiDivLineArray[j]=temp;
	}
	bool isNestedColumnChange=false;
	int noofintersectLine=0;
	for(int i=0;i<count;i++)
	{
		//int j=(i==0)?0:s->multiDivLineArray[i-1];
		if(i==0)
		{
			start=0;
			end=s->multiDivLineArray[i];
		}
		else
		{
			start=end;
			end=s->multiDivLineArray[i];
		}
		for(int j=start;j<end;j++)
		{
			if(j==0)
			{
				if(s->n[i]<xoutRound(s->stringArray[j]->xMax))
				{
					if(s->n[i]+s->n[i+1]>=xoutRound(s->stringArray[j]->xMax))
					{
						s->stringArray[j]->isMultiColumnTable=true;
						noofintersectLine++;
						isNestedColumnChange=true;
						interserctColumnArray[c]=j;
						c++;
					}
				}
			}
			else
			{
				if(s->n[i]<xoutRound(s->stringArray[j]->xMax-s->stringArray[j]->xMin))
				{	
					if(s->n[i]+s->n[i+1]>=xoutRound(s->stringArray[j]->xMax-s->stringArray[j]->xMin))
					{
						s->stringArray[j]->isMultiColumnTable=true;
						noofintersectLine++;
						isNestedColumnChange=true;
						interserctColumnArray[c]=j;
						c++;
					}
				}
			}
		}
	}

	if(isNestedColumnChange)
	{
		for(int i=0;i<count;i++)
		{
			if(i==0)
			{
				start=0;
				end=s->multiDivLineArray[i];
			}
			else
			{
				start=end;
				end=s->multiDivLineArray[i];
			}   //	int j=(i==0)?0:s->multiDivLineArray[i-1];

			for(int j=start;j<end;j++)
			{
				if(j<length&&s->stringArray[j]->isMultiColumnTable&&i<count-1)
				{
					bool isPresent=false;
					for(int l=0;l<noofintersectLine;l++)
					{
						if(interserctColumnArray[l]==j)
						{
							isPresent=true;
						}
					}
					if(isPresent)
					{
						if(xoutRound(s->stringArray[j]->yMin)>xoutRound(s->stringArray[j+1]->yMin))
						{ 
							HtmlString *tmp=s->stringArray[j];  
							s->stringArray[j]=s->stringArray[j+1];
							s->stringArray[j+1]=tmp;
						}
					}
					//if(i==0)
					//{
					//	HtmlString *tmp=s->stringArray[s->multiDivLineArray[i]];
					//	s->stringArray[s->multiDivLineArray[i]]=s->stringArray[s->multiDivLineArray[i+1]];
					//	s->stringArray[s->multiDivLineArray[i+1]]=tmp;
					//	s->n[i]+=s->n[i+1];
					//}
					//else if(xoutRound(s->stringArray[s->multiDivLineArray[i]]->yMin)< xoutRound(s->stringArray[j]->yMin))
					//{	
					//	HtmlString *tmp=s->stringArray[s->multiDivLineArray[i]];
					//	s->stringArray[s->multiDivLineArray[i]]=s->stringArray[s->multiDivLineArray[i-1]];
					//	s->stringArray[s->multiDivLineArray[i-1]]=tmp;
					//	s->n[i]+=s->n[i+1];
					//	//joining the missed XminMultiCoumn
					//	s->multiDivLineArray[i]+=1;
					//}
					//else
					//{
					//	s->multiDivLineArray[i]+=1;
					//	s->n[i]+=s->n[i+1];
					//}
				}
			}
		}


		//int temp=0;
		//int intersectColumnNo=0;
		////Recalculating Lines end
		//for(int j=0;j<count;j++)
		//{			
		//	int k=(j==0)?0:s->multiDivLineArray[j-1];
		//	bool b=false;
		//
		//	if(k<length&&j<count-1&&s->stringArray[k]->isMultiColumnTable)
		//	{				
		//		if(temp==0&&j>0)
		//		{
		//			s->multiDivLineArray[temp]=s->multiDivLineArray[j-1];
		//			temp++;
		//		}
		//		
		//		s->multiDivLineArray[temp]=s->multiDivLineArray[j+1];				
		//		s->n[temp]=s->n[j];
		//		temp++;
		//		
		//		intersectColumnNo=s->multiDivLineArray[j];
		//		b=true;
		//	}
		//	if(intersectColumnNo!=k&&!b)
		//	{ 
		//		s->multiDivLineArray[temp]=k;
		//		s->n[temp]=s->n[j];
		//		temp++;
		//	}

		//	if(k==length)
		//	{
		//		s->columns=count-noofintersectLine;
		//		break;
		//	}
		//}
		temp=0;
		for(int i=0;i<count;i++)
		{
			int x=s->multiDivLineArray[i]; 
			bool isPresent=false;
			for(int k=0;k<noofintersectLine;k++)
			{
				if(interserctColumnArray[k]==x-1)
				{
					isPresent=true;
				}
			}
			if(isPresent)
			{
				s->multiDivLineArray[temp]=x+1;
				temp++;
			}
			else
			{
				bool isTrue=true;
					if(temp>0)
					{
						for(int l=0;l<temp;l++)
						{
							if(s->multiDivLineArray[l]>=x)
								isTrue=false;
						}
					}
					if(isTrue)
					{
						s->multiDivLineArray[temp]=x;
						temp++;
					}
				}
				s->columns=count-noofintersectLine;
			
		}
	}
	else
	{
		s->columns=count-noofintersectLine;
	}

	
	for(int i=0;i<s->columns;i++)
	{		
		int t=0;
		if(i==0)
		{
			start=0;
			end=s->multiDivLineArray[i];
		}
		else
		{
			start=end;
			end=s->multiDivLineArray[i];
		}
		int xMin=0;
		if(i>0)
		{
			xMin=xoutRound(s->stringArray[start]->xMin);
			for(int j=start;j<end;j++)
			{ 
				if(xMin>xoutRound(s->stringArray[j]->xMin))
					xMin=xoutRound(s->stringArray[j]->xMin);
			} 

			if(i>1)
			{ 
				for(int j=0;j<i-1;j++)
					t+=s->n[j];
				s->n[i-1]=xMin-t;				
			}
			else if(i==1)
				s->n[0]=xMin;
		}
		if(i==s->columns-1)
		{
			s->n[i]=pageWidth-(t+s->n[i-1]);
		}
		SetTopMargins(s,start,end);
		
	}	
	s->lastLine=str1[length-1];
	return s;
}


HtmlString* HtmlPage::SeparateDiv(HtmlString *string,int *xArray,int count,HtmlString *str1[],int length)
{
	
	lineStringCount=length;
	int xValue=0;	
	
	int temp=0;
	bool isLastColumn=false;
	string->lastLine=str1[length-1];
	int yLength=0;
	
	for(int i=0;i<count;i++)
    {
        for(int j=0;j<count;j++)
        {
            if(xArray[i]<xArray[j])
            {
                temp=xArray[i];
                xArray[i]=xArray[j];
                xArray[j]=temp;
            }
        }
    }
	temp=0;

	//Get the list of Yvalues.
	int *yMinList=new int[length]; 
	yMinList[0]=xoutRound(str1[0]->yMin);
	temp++;
	for(int i=0;i<length;i++)
	{
		bool isPresent=false;
		if(temp>0)
		{
			for(int j=0;j<temp;j++)
			{
				if(yMinList[j]==xoutRound(str1[i]->yMin))
				isPresent=true;
			}
		}	
		if(!isPresent)
		{
			yMinList[temp]=xoutRound(str1[i]->yMin);
			temp++;
		}
	}
	yLength=temp;
	temp=0;

	//Ascending yValues.
	for(int i=0;i<yLength;i++)
    {
        for(int j=0;j<yLength;j++)
        {
            if(yMinList[i]<yMinList[j])
            {
                temp=yMinList[i];
                yMinList[i]=yMinList[j];
                yMinList[j]=temp;
            }
        }
    }
	temp=0;
	float totalWidth=0;
	
	for(int i=0;i<count;i++)
	{
		
		xValue=xArray[i];
		totalWidth=0;
		if(i>0)
		{			
			for(int k=0;k<i-1;k++)			  
			{
				totalWidth+= string->n[k];
			}									
			string->n[i-1]=xArray[i]-totalWidth;
			
		}
		else
			string->n[i-1]=xArray[i];

		if(i==count-1)
		{
			int wi=0;
			wi=pageWidth-xValue;
			string->n[i]=wi;
		}
		string->multiDivLineArray[i]=temp;
		for(int j=0;j<length;j++)
		{
			if(length>count&&count>1&&i==count-1)
			{
				isLastColumn=true;										
			}
			if(xValue==xoutRound(str1[j]->xMin))
			{
				string->stringArray[temp]=str1[j];
				temp++;
			}
		}		
	
		GString iStr;
		
	
		if(!string->isPreviousLine)
		{			
			int TotalColumn=GetNoofColumn(string,temp);
			bool isexist=false;
			for(int j=0;j<TotalColumn;j++)
			{
				bool isPresent=false;
				for(int i=0;i<previousLineStartString->multiColumncount;i++)
				{
					if(xoutRound(string->stringArray[j]->xMin)== xoutRound(previousLineStartString->stringArray[i]->xMin))
					{
						isPresent=true;
					}
				}
				if(isPresent)
				{
					isexist=true;
				}
				else
				{
					isexist=false;
					break;
				}
			}
			
			if(TotalColumn==previousLineStartString->columns)
			{
				int l=previousLineStartString->multiColumncount;
				
				for(int k=string->multiDivLineArray[i];k<temp;k++)
				{
					if(!isexist)
					{
						if(CheckIsTextPresent(previousLineStartString,l,string->stringArray[k]))
						{}
					}
					else
						if(!CheckIsTextPresent(previousLineStartString,l,string->stringArray[k]))
						{
							previousLineStartString->stringArray[l]=string->stringArray[k];
							l++;
						}
				}		
				previousLineStartString->lastLine=string->lastLine;	
				previousLineStartString->multiColumncount=l;		
				
				UpdateTopMargin(previousLineStartString);	
				string->isPreviousLine=false;
			}
		}

		else
		{
			string=	SetTopMargin(string,string->multiDivLineArray[i],temp);				
		}
		
	}
	

	bool isMultiColumnWithDifferentXposition=false;
	for(int i=0;i<count&&count>1;i++)
	{	
		int tempwidth=string->n[i];
		int width=0;
		if(string->n[i] <= 0)
		{
			width=xoutRound((pageWidth/*-((72*scale)/2)*/));
				for(int j=0;j<i;j++)
				{			
					width-=string->n[j];
				}
				string->n[i]=width;
		}
		if(i==0)
		{
			if(string->n[i]<xoutRound(string->stringArray[i]->xMax))
			{
				isMultiColumnWithDifferentXposition=true;
				break;
			}
		}
		else
		{
			if(string->n[i]<xoutRound(string->stringArray[i]->xMax-string->stringArray[i]->xMin))
			{
				isMultiColumnWithDifferentXposition=true;
				break;
			}
		}
	}

	if(isMultiColumnWithDifferentXposition)
	{
		string->isMultiColumnTable=true;
		temp=0;
		int c=0;

	
		for(int i=0;i<length;i++)
		{
			if(temp>0)
			{
				string->stringArray[temp-1]->isEndLine=true;
				string->multiDivLineArray[i-1]=temp;
			}
			string->stringArray[temp]=str1[c];
			temp++; 
			c++;
				
		}
		string->stringArray[temp-1]->isEndLine=true;
		string->lineCount=yLength;
		string->multiDivLineArray[yLength-1]=temp;	
		
		temp=0;		
	}	

	string->columns=count;
	string->multiColumncount=length;	
	return string;
}

 //int HtmlPage::CalculateNoofColumn(HtmlString *str1[],int length)
 //{
	// int noofColumn=0;
	// int *columnArray=new int[length];
	// for(int i=0;i<length;i++)
	// {
	//	 int xMin=xoutRound(str1[i]->xMin);
	//	 if(xMin!=0)
	//	 {
	//		 for(int j=0;j<length;j++)
	//		 {
	//			 if(xMin==xoutRound(str1[j]->xMin))
	//			 {
	//				 if(noofColumn>0)
	//				 {
	//					 bool isPresent=false;
	//					 for(int k=0;k<noofColumn;k++)
	//					 {
	//						 if(columnArray[k]==xMin)
	//						 {
	//							 isPresent=true;
	//						 }
	//					 }
	//					 if(!isPresent)
	//					 {
	//						 columnArray[noofColumn]=xMin;
	//						 noofColumn++;
	//					 }
	//				 }
	//				 else
	//				 {
	//					 columnArray[noofColumn]=xMin;
	//					 noofColumn++;
	//				 }
	//				/* str1[j]->xMin=0;
	//				 str1[i]->xMin=0;*/
	//			 }
	//		 }
	//	 }
	// }
	// 
 //return noofColumn>2?noofColumn-1:noofColumn;
 //}


HtmlString* HtmlPage::SetTopMargin(HtmlString *tmp1,int startingPoint,int count,HtmlString *str[])
{
	return tmp1;
}

HtmlString* HtmlPage::SetTopMargin(HtmlString *tmp1,int startingPoint,int count)
{
	int yMinvalue=xoutRound(tmp1->stringArray[startingPoint]->yMax);	
	int difference=0;
	int yMax=0;
	bool isTotallineMovedinPreviousLine=false;
	
	if(tmp1->previousLineYmax==0)
	{
		tmp1->stringArray[startingPoint]->marginTop=xoutRound(tmp1->stringArray[startingPoint]->yMin);
		yMax=xoutRound(tmp1->stringArray[startingPoint]->yMin);
	}
	else
	{
		if(yMax<tmp1->stringArray[startingPoint]->yMax)
			yMax=tmp1->stringArray[startingPoint]->yMax;
		tmp1->stringArray[startingPoint]->marginTop=xoutRound(tmp1->stringArray[startingPoint]->yMin)-tmp1->previousLineYmax;
		if(tmp1->isPreviousLine)
		{
			if(tmp1->stringArray[startingPoint]->marginTop<=-3)
			{		
				int TotalColumn=GetNoofColumn(tmp1,count);
				bool isexist=false;
				if(previousLineStartString->columns>=lineStringCount)
				{
					for(int j=0;j<lineStringCount;j++)
					{
						bool isPresent=false;
						for(int i=0;i<previousLineStartString->multiColumncount;i++)
						{
							if(xoutRound(stringArry[j]->xMin)== xoutRound(previousLineStartString->stringArray[i]->xMin))
							{
								isPresent=true;
							}
						}
						if(isPresent)
						{
							isexist=true;
						}
						else
						{
							isexist=false;
							break;
						}
					}
				}
				else
				{
					for(int j=0;j<previousLineStartString->multiColumncount;j++)
					{
						bool isPresent=false;
						for(int i=0;i<lineStringCount;i++)
						{
							if(xoutRound(previousLineStartString->stringArray[j]->xMin)==xoutRound(stringArry[i]->xMin))
							{
								isPresent=true;
							}
						}
						if(isPresent)
						{
							isexist=true;
						}
						else
						{	
							isexist=false;
							break;
						}
					}
				}
				if(isexist)
				{
					bool isTextPresent=false;
					int temp=previousLineStartString->multiColumncount;
					for(int i=0;i<count;i++)
					{
						isTextPresent=CheckIsTextPresent(previousLineStartString,temp,stringArry[i]/*tmp1->stringArray[i]*/);
						if(!isTextPresent)
						{
							previousLineStartString->stringArray[temp]=stringArry[i];
							temp++;
						}						
					}	
					if(!tmp1->isPreviousLine)
					{
						for(int i=startingPoint+1;i<count;i++)
						{
							int temp=0;
							if(yMax<tmp1->stringArray[i]->yMax)
								yMax=xoutRound(tmp1->stringArray[i]->yMax);
							temp=xoutRound(tmp1->stringArray[i]->yMin)-yMinvalue;  
							tmp1->stringArray[i]->marginTop=temp;
							yMinvalue=xoutRound(tmp1->stringArray[i]->yMax);						
						}
						return tmp1->lastLine;
					}
					previousLineStartString->lastLine=tmp1->lastLine;		
					isTotallineMovedinPreviousLine=true;					
					previousLineStartString->multiColumncount=temp;		
					tmp1->isPreviousLine=false;
					previousLineStartString->isPreviousLine=false;
					UpdateTopMargin(previousLineStartString);
				}
				else
				{					
					HtmlString *t=GetMaxY(previousLineStartString,previousLineStartString->multiColumncount);
					HtmlFont *font=getFont(t);
					if(font->size-1<=t->height+tmp1->stringArray[startingPoint]->marginTop)
					{
						if(!t->isFirst)
						{
							t->height+=tmp1->stringArray[startingPoint]->marginTop;				
							t->isFirst=true;
						}									
					}					 
					if(t->isFirst)	
					{
						tmp1->stringArray[startingPoint]->marginTop=0;	
					}
				}
			}
			}
			else if(!tmp1->isPreviousLine)
			{
				for(int i=startingPoint+1;i<count;i++)
				{
					int temp=0;
					if(yMax<tmp1->stringArray[i]->yMax)
						yMax=xoutRound(tmp1->stringArray[i]->yMax);
					temp=xoutRound(tmp1->stringArray[i]->yMin)-yMinvalue;  
					tmp1->stringArray[i]->marginTop=temp;
					yMinvalue=xoutRound(tmp1->stringArray[i]->yMax);						
				}
				return tmp1->lastLine;
			}
			}

	if(!isTotallineMovedinPreviousLine)
	{
		for(int i=startingPoint+1;i<count;i++)	
		{		
		int temp=0;
		if(yMax<tmp1->stringArray[i]->yMax)
			yMax=xoutRound(tmp1->stringArray[i]->yMax);
		temp=xoutRound(tmp1->stringArray[i]->yMin)-yMinvalue;  
		tmp1->stringArray[i]->marginTop=temp;
		yMinvalue=xoutRound(tmp1->stringArray[i]->yMax);
		if(tmp1->stringArray[i]->marginTop<0)
		{
			bool b=true;
		}		
		yMinvalue=xoutRound(tmp1->stringArray[i]->yMax);
		}
	}

	return tmp1;
}


bool HtmlPage::CheckIsPresent(int *xvalue,int count,int x)
{
	bool IsPresent=false;
	for(int i=0;i<count;i++)
	{
		if(x==xvalue[i])
		{					
			IsPresent=true;
			break;
		}	
	}
	return IsPresent;
}

bool HtmlPage::CheckIsTextPresent(HtmlString *tmp,int length,HtmlString *searchString)
{
	bool IsPresent=false;
	for(int i=0;i<length;i++)
	{
		if(searchString->htext==tmp->stringArray[i]->htext)
		{					
			IsPresent=true;
			break;
		}
	}
	return IsPresent;
}
bool HtmlPage::CheckWhetherTextIsPresent(HtmlString *tmp[],int length,HtmlString *searchString)
{
	bool IsPresent=false;
	for(int i=0;i<length;i++)
	{
		if(searchString->htext==tmp[i]->htext)
		{					
			IsPresent=true;
			break;
		}
	}
	return IsPresent;
}

int HtmlPage::GetNoofColumn(HtmlString *string,int length)
 { 
	 int *xArray=new int[length];
	 int count=0;
	 bool IsPresent=false;

	 for(int i=0;i<length;i++)
	 {
		 if(i==0)
		 {
			 xArray[count]=xoutRound(string->stringArray[i]->xMin);
			 count++;
		 }
		 else
		 {
			 IsPresent= CheckIsPresent(xArray,count,xoutRound(string->stringArray[i]->xMin));
			 if(!IsPresent)
			 {
				 xArray[count]=xoutRound(string->stringArray[i]->xMin);	
				 count++;
			 }
		 }
	 }
	 delete []xArray;
	 return count;
 }

void HtmlPage::UpdateTopMargin(HtmlString *string)
{
	int *xArray=new int[previousLineStartString->multiColumncount];
	int temp=0;
	int length=previousLineStartString->multiColumncount;
	int xValue=0;
	HtmlString *localString=string->stringArray[1];
	int count=0;
	for(int j=0;j<string->multiColumncount;j++)
	{			
		localString->stringArray[j]=string->stringArray[j];
	}
	
	bool IsPresent=false;
	for(int i=0;i<previousLineStartString->multiColumncount;i++)
	{
		if(i==0)
		{
			xArray[temp]=xoutRound(previousLineStartString->stringArray[i]->xMin);
			temp++;
		}
		else
		{
			IsPresent=CheckIsPresent(xArray,temp,xoutRound(previousLineStartString->stringArray[i]->xMin));
			if(!IsPresent)
			{
				xArray[temp]=xoutRound(previousLineStartString->stringArray[i]->xMin);	
				temp++;
			}
		}
	}
	string->columns=temp;
	
	temp=0;
	for(int i=0;i<count;i++)
    {
        for(int j=0;j<count;j++)
        {
            if(xArray[i]<xArray[j])
            {
                temp=xArray[i];
                xArray[i]=xArray[j];
                xArray[j]=temp;
            }
        }
    }

	temp=string->columns;
	for(int i=0;i<temp;i++)
	{
		
		xValue=xArray[i];
		if(i>1)
		{
			float totalWidth=0;
			for(int k=0;k<i-1;k++)			  
			{
				totalWidth+= string->n[k];
			}									
			string->n[i-1]=xArray[i]-totalWidth;
		}
		else
			string->n[i-1]=xArray[i];
		string->multiDivLineArray[i]=count;
		for(int j=0;j<length;j++)
		{			
			if(xValue==xoutRound(localString->stringArray[j]->xMin))
			{
				string->stringArray[count]=localString->stringArray[j];					
				count++;
			}
		}			
		
		SetTopMargin(string,string->multiDivLineArray[i],count);	
	}

		bool isMultiColumnWithDifferentXposition=false;
		for(int i=0;i<string->columns&&string->columns>1;i++)
	{
		int tempwidth=string->n[i];
		int width=0;
		if(string->n[i]<0&&i>0)
		{
			width=xoutRound((pageWidth/*-((72*scale)/2)*/));
				for(int j=0;j<i;j++)
				{			
					width-=string->n[j];
				}
				string->n[i]=width;
		}
		if(i==0)
		{
			if(string->n[i]<xoutRound(string->stringArray[i]->xMax))
			{
				isMultiColumnWithDifferentXposition=true;
				break;
			}
		}
		else
		{
			int width=string->n[i];
			if(string->n[i]<xoutRound(string->stringArray[i]->xMax-string->stringArray[i]->xMin))
			{
				isMultiColumnWithDifferentXposition=true;
				break;
			}
		}
	}

	//if(isMultiColumnWithDifferentXposition)
	//{
	//	string->isMultiColumnTable=true;
	//
	//	temp=0;
	//	int c=0;	
	//	for(int i=0;i<length;i++)
	//	{
	//		if(temp>0)
	//		{
	//			string->stringArray[temp-1]->isEndLine=true;
	//			string->multiDivLineArray[i-1]=temp;
	//		}							
	//	    string->stringArray[temp]=localString->stringArray[i];
	//		temp++; 
	//		c++;
	//			outfile << "UpdateTopMargin"<<std::endl;
	//			outfile<< string->n[i] <<std::endl;
	//			fputs("UpdateTopMargin\n",file);
	//			fprintf(file,"%d",string->n[i]);
	//			fprintf(file,"%d\n",xoutRound(string->stringArray[i]->xMax-string->stringArray[i]->xMin));
	//			outfile<< xoutRound(string->stringArray[i]->xMax-string->stringArray[i]->xMin)<<std::endl;
	//			GString *s=new GString(string->stringArray[i]->htext);	
	//			fputs(s->getCString(),file);
	//			 //outfile<< s << std::endl;
	//			delete s;
	//		
	//	}
	//	string->stringArray[temp-1]->isEndLine=true;
	////	string->lineCount=yLength;
	//	//string->multiDivLineArray[yLength-1]=temp;	
	//	//string=	SetTopMargin(string,0,temp);
	//	temp=0;		
	//}
	//outfile << "Update top margin ispreviousline"<<std::endl;
	string->isPreviousLine=false;
}

HtmlString* HtmlPage:: DrawTable(FILE *pageFile,int page,HtmlString *tmp1)
{
	GString *str,*str1;	
	
	int column=tmp1->columns;
	int row=tmp1->rows;
	int count=0;
	int marginTop=0;
	int divWidth;
	int *topMargin;
	topMargin=new int[row];
	if(tmp1->rows>0)
	{
		if(tmp1->columns>1)
		{
			fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth);
			for(int i=0;i<column;i++)
			{
				count=i;
				if(count==0)
				{
					divWidth=xoutRound(tmp1->stringArray[count+1]->xMin);
				}
				else if(count!=column-1)
				{
					divWidth=xoutRound(tmp1->stringArray[count+1]->xMin-tmp1->stringArray[count]->xMin);
				}
				else
				{
					//divWidth=xoutRound(tmp1->stringArray[count]->xMax-tmp1->stringArray[count]->xMin);
					divWidth=xoutRound((pageWidth-((72*scale)/2))-tmp1->stringArray[count]->xMin);
					//divWidth=xoutRound(pageWidth/scale)-(tmp1->stringArray[count]->xMin/scale)
				}
				fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",divWidth);
				for(int j=0;j<row;j++)
				{					
					if(i>0)
						marginTop=topMargin[j];						
					str=new GString(tmp1->stringArray[count]->htext);	
					int lineHeight=xoutRound(tmp1->stringArray[count]->yMax)- xoutRound(tmp1->stringArray[count]->yMin);
					str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[count]->fontpos, str,tmp1->stringArray[count]->paragraphStyle,i,marginTop,xoutRound(tmp1->stringArray[count]->height)); 
					fputs(str1->getCString(),pageFile);	
					if(i==0)
					{
						topMargin[j]=tmp1->stringArray[count]->marginTop;
					}
					if(row>0&&j!=row-1)
						count+=column;						
				}		 			 

				fputs("</div>\n",pageFile);
			}		
			fputs("</div>\n",pageFile);
		}		
	}

	count=(tmp1->columns*tmp1->rows)-1;
	return tmp1->stringArray[count];
}

void HtmlPage::DecreasePreviousLineHeight(HtmlString *string,int height,int topmargin)
{
	for(int i=0;i<string->multiColumncount;i++)
	{
		if(string->stringArray[i]->yMax>=height)
		{
			string->stringArray[i]->height+=topmargin;
		}	
	}
}

HtmlString* HtmlPage:: DrawMultiColumnTables(FILE *pageFile,int page,HtmlString *tmp1)
{
	GString *str,*str1;	
	int divWidth=0;
	int start=0;
	int end=0;
	int topMargin=0;
	int paddingLeft=0;
	int Totalwidth=0;
	int x=0;
	fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth);
	for(int k=0;k<tmp1->columns;k++)
	{
		int startMargin=0;
		if(k==0)
		{
			start=0;
			end=tmp1->multiDivLineArray[k];
		}
		else
		{
			startMargin=end;
			start=end;
			end=tmp1->multiDivLineArray[k];
		}
		divWidth=tmp1->n[k];		
		if(tmp1->columns==1)
		{
			if(xoutRound(tmp1->stringArray[0]->yMin)!=xoutRound(GetMinY(tmp1,end)))
			{
				x=xoutRound(tmp1->stringArray[0]->yMin)-xoutRound(GetMinY(tmp1,end));
				x-=tmp1->stringArray[0]->marginTop;
			}
		}
		else
		{
			x=tmp1->stringArray[startMargin]->marginTop;
		}
		fprintf(pageFile,"<span style=\"width:%d;float:left;border:none;margin: %dpx 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",divWidth,x);
		for(int j=start;j<end;j++)
		{
			str=new GString(tmp1->stringArray[j]->htext);
			int lineHeight=xoutRound(tmp1->stringArray[j]->yMax)-xoutRound(tmp1->stringArray[j]->yMin);
			if(j!=start)
			{
				topMargin=tmp1->stringArray[j]->marginTop;				
			}
			else
			{
				if(x!=tmp1->stringArray[j]->marginTop)
					topMargin=tmp1->stringArray[j]->marginTop-x;
				else
					topMargin=0;
			}
			if(start!=0&&xoutRound(tmp1->stringArray[j]->xMin)>Totalwidth)
			{
				paddingLeft=xoutRound(tmp1->stringArray[j]->xMin)-Totalwidth;
			}
			str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[j]->fontpos, str,tmp1->stringArray[j]->paragraphStyle,k,topMargin,false,xoutRound(tmp1->stringArray[j]->height),paddingLeft);	
			paddingLeft=0;
			fputs(str1->getCString(),pageFile);
		}
		Totalwidth+=divWidth;
		fputs("</span>\n",pageFile);
	}
	fputs("</div>\n",pageFile);

	return tmp1->lastLine;
}
HtmlString* HtmlPage:: DrawMultiColumnTable(FILE *pageFile,int page,HtmlString *tmp1)
{		
	GString *str,*str1;	
	int count=0;
	int marginTop=0;
	int divWidth=0;
	bool f=false;
	int tempyMax=0;
	bool isMultiDiv=false;
	int yMax=0;
	int totalwidth=0;

	if(tmp1->isMultiColumnTable)
	{		
		int temp=0;					
		int lineNO=0;
		int endColumnDivWidth=0;
		int previousXMaxvalue=0,previousXMinvalue=0;
		int start=0,end=tmp1->multiColumncount;
		int Baseline=xoutRound(tmp1->stringArray[0]->yMax);
		int *ListofYmax=new int[tmp1->multiColumncount];
		int column=0;
		
		int Top=0;
		bool canEnter=true;
		int xMax=0;
		tmp1->multiDivLineArray=new int[tmp1->multiColumncount];
		HtmlString *previousLine;
		int previousLineYmaxvalue=0;
		int count=0;
		
		for(int i=0;i<tmp1->multiColumncount;i++)
		{
			if(xMax>tmp1->stringArray[i]->xMin)
			{
				tmp1->multiDivLineArray[count]=i;
				count++;
				xMax=tmp1->stringArray[i]->xMax;
			}

			if(tmp1->stringArray[i]->xMax>xMax)
			{
				xMax=tmp1->stringArray[i]->xMax;
			}
			
		}
		tmp1->multiDivLineArray[count]=tmp1->multiColumncount;
		count++;
		DrawInnerMultiColumnTable(pageFile,page,tmp1,count);		
	}
	else
	{
		
		int start=0;
		int end=0;
		fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth);
		for(int k=0;k<tmp1->columns;k++)
		{
			divWidth=tmp1->n[k];	
			totalwidth+=divWidth;
			if(k==0)
			{
				start=0;
				end=tmp1->multiDivLineArray[k];
			}
			else
			{
				start=end;
				end=tmp1->multiDivLineArray[k];
			}

			int temp=k==tmp1->columns-1?tmp1->multiColumncount:tmp1->multiDivLineArray[k];		
			
			
			if(tmp1->columns==1)
				divWidth=pageWidth;
			

			 if(divWidth==0)
			 {
				 divWidth=pageWidth-totalwidth;
			 }

			
			fprintf(pageFile,"<span style=\"width:%d;float:left;border:none;margin: %dpx 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",divWidth,tmp1->stringArray[tmp1->multiDivLineArray[k]]->marginTop);							
			
			for(int j=start;j<end;j++)
			{ 
				if(tmp1->isInterSect&&j==tmp1->multiDivLineArray[k])
				{
					marginTop=0;
				}
				if(yMax<tmp1->stringArray[j]->yMax)
				yMax=xoutRound(tmp1->stringArray[j]->yMax);
				if(j==tmp1->multiDivLineArray[k])
					marginTop=0;
				else
				{
					marginTop=tmp1->stringArray[j]->marginTop;
				}
				if(marginTop<0)
				{
					previousLineStartString;
					//marginTop=0;
				}
					f=false;					
					if(tmp1->stringArray[j]->htext)
						str=new GString(tmp1->stringArray[j]->htext);				
					else
						str=new GString(tmp1->stringArray[j]->htext2);
						int lineHeight=xoutRound(tmp1->stringArray[j]->yMax)-xoutRound(tmp1->stringArray[j]->yMin);
						//str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[j]->fontpos, str,tmp1->stringArray[j]->paragraphStyle,k,marginTop,f,xoutRound(tmp1->stringArray[j]->height));	
						fputs(str1->getCString(),pageFile);	
						count=j;
				if(tmp1->columns==tmp1->multiColumncount)
				{			
					if(k!=tmp1->columns-1)
						count++;
					break;
				}	
			}
			fputs("</span>\n",pageFile);
		}
		
		fputs("</div>\n",pageFile);
		
	}
	
	if(isMultiDiv&&tmp1->lastLine!=NULL)
	{
		tmp1->lastLine==tmp1->lastLine->yxNext;
	}
	previousLineYmax=xoutRound(tmp1->lastLine->yMax);
	previousLineYmax=yMax;
	return tmp1->lastLine;	
}

int HtmlPage::GetListOfYmax(int maxY,HtmlString *tmp1)
{
	int yMax=0;
	for(int i=0;i<tmp1->multiColumncount;i++)
		{
			if(maxY>=xoutRound(tmp1->stringArray[i]->yMin))
			{
				if(yMax<xoutRound(tmp1->stringArray[i]->yMax))
				{
					yMax=xoutRound(tmp1->stringArray[i]->yMax);
				}
			}
		}

	return yMax;
}

void HtmlPage::DrawInnerMultiColumnTable(FILE *pageFile,int page,HtmlString *tmp1,int count)
{
	int width=0;
	GString *str,*str1;
	int Baseline=0;
	int Top=0;
	bool canEnter=true;
	int start=0,end=0;
	int column=0;
	int totalwidth=0;
	int yMax=0;
	for(int i=0;i<count;i++)
	{
		fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth);
		if(i==0)
			end=tmp1->multiDivLineArray[i];
		else
		{
			start=end;
			end=tmp1->multiDivLineArray[i];
			column=0;
			totalwidth=0;
		}		
		for(int j=start;j<end;j++)
		{	
			if(yMax<tmp1->stringArray[j]->yMax)
				yMax=xoutRound(tmp1->stringArray[j]->yMax);
			if(totalwidth>0&&j!=end-1)
				width=xoutRound(tmp1->stringArray[j+1]->xMin)-totalwidth;
			if(j==end-1)
			{
				width=pageWidth-xoutRound(tmp1->stringArray[j]->xMin);
			}
			if(j==start&&start!=end-1)
				width=xoutRound(tmp1->stringArray[j+1]->xMin);
			if(start==end-1)
				width=pageWidth;	
			if(previousLineYmax>0)
			tmp1->stringArray[j]->marginTop=xoutRound(tmp1->stringArray[j]->yMin)-previousLineYmax;
			if(width>pageWidth)
			{
				width=pageWidth-xoutRound(tmp1->stringArray[j]->xMin);
			}
			fprintf(pageFile,"<span style=\"width:%d;float:left;border:none;margin: %dpx 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",width,tmp1->stringArray[j]->marginTop);
			str=new GString(tmp1->stringArray[j]->htext);		
			int lineHeight=xoutRound(tmp1->stringArray[j]->yMax)-xoutRound(tmp1->stringArray[j]->yMin);
		//	str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[j]->fontpos, str,tmp1->stringArray[j]->paragraphStyle,column,0,false,xoutRound(tmp1->stringArray[j]->height));	
			fputs(str1->getCString(),pageFile);	
			fputs("</span>\n",pageFile);
			column++;
			totalwidth+=width;
		}
		fputs("</div>\n",pageFile);
		Top=Baseline;		
		previousLineYmax=yMax;
	}
	
}

//void HtmlPage::DrawInnerMultiColumnTable(FILE *pageFile,int page,HtmlString *tmp1,int start,int end,int maxX)
//{
//	int width=0;
//	GString *str,*str1;
//	int count=0;
//	
//	fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth);
//	for(int i=start;i<end;i++)
//	{
//		if(tmp1->stringArray[i]->xMin<maxX)
//		{
//			fputs("</div>\n",pageFile);
//			maxX=0;
//			count=0;
//			DrawInnerMultiColumnTable(pageFile,page,tmp1,i,end,maxX);
//			break;
//		}
//		else
//		{
//			if(i!=end-1&&tmp1->stringArray[i+1]->xMin>tmp1->stringArray[i]->xMax)
//			{
//				width=tmp1->stringArray[i+1]->xMin;
//			}
//			else
//			{
//				width= pageWidth-tmp1->stringArray[i]->xMin;
//			}	
//		
//			/*if(count==0)
//			{
//				if(tmp1->stringArray[i]->xMin>minX)
//					count++;
//			}*/
//			fprintf(pageFile,"<span style=\"width:%d;float:left;border:none;margin: %dpx 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",width,tmp1->stringArray[i]->marginTop);
//			str=new GString(tmp1->stringArray[i]->htext);		
//			str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[i]->fontpos, str,tmp1->stringArray[i]->paragraphStyle,count,0,false);	
//			fputs(str1->getCString(),pageFile);	
//			maxX=xoutRound(tmp1->stringArray[i]->xMax);
//			count++;
//			fputs("</span>\n",pageFile);
//		}	
//		if(i==end-1)
//		{
//			fputs("</div>\n",pageFile);
//		}
//	}
//}


//
//HtmlString* HtmlPage:: DrawMultiColumnTable(FILE *pageFile,int page,HtmlString *tmp1,bool isRightToLeft)
//{			
//	GString *str,*str1;	
//	int count=0;
//	int marginTop=0;
//	int divWidth;
//	bool f=false;
//	int tempyMax=0;
//	fprintf(pageFile,"<div style=\"width:%d;float:left;border:none;margin: %dpx 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",pageWidth,xoutRound(tmp1->marginTop));
//	for(int k=0;k<tmp1->columns;k++)
//	{		
//		divWidth=tmp1->n[k];
//		fprintf(pageFile,"<span style=\"width:%d;float:left;border:none;margin: 0px 0px 0px 0px;padding: 0px;border:none;overflow: hidden;\">\n",divWidth);					
//		
//			for(int j=0;j<tmp1->multiColumncount;j++)
//			{ 
//			
//				if(j==0||j==count)	
//				{
//					marginTop=0;
//					f=true;
//				}
//				else
//				{					
//					marginTop=tmp1->stringArray[j]->marginTop;	
//					f=false;
//				}
//				if(xoutRound(tmp1->stringArray[j]->xMin)==divWidth)
//				{				
//					str=new GString(tmp1->stringArray[j]->htext);		
//
//					str1=fonts->getMultiColumnCSStyle(tmp1->stringArray[j]->fontpos, str,tmp1->stringArray[j]->paragraphStyle,k,marginTop,f);	
//
//					fputs(str1->getCString(),pageFile);	
//				}
//			count=j;
//		}
//		fputs("</span>\n",pageFile);
//	}
//	fputs("</div>\n",pageFile);
//	
//	tempyMax=xoutRound(tmp1->stringArray[count]->yMax);
//	for(int i=1;i<tmp1->columns;i++)
//	{		
//		if(tmp1->columns==2&&tmp1->multiColumncount==2)
//		{
//			if(xoutRound(tmp1->stringArray[0]->yMin)==xoutRound(tmp1->stringArray[1]->yMin))
//				count=1;
//		}
//		else
//		{
//			if(tempyMax<xoutRound(tmp1->stringArray[tmp1->multiDivLineArray[i-1]-1]->yMax))
//			{
//				tempyMax=xoutRound(tmp1->stringArray[tmp1->multiDivLineArray[i-1]-1]->yMax);
//				count=tmp1->multiDivLineArray[i-1]-1;
//			}	
//		}
//	}
//	return tmp1->lastLine;
//}

void HtmlPage::dump(FILE *f, int pageNum) 
{	
  /* if (complexMode)
  {*/
		
	/*std::ofstream outfile ("dump.txt");
	outfile << "Dump"<<std::endl;
	outfile.close();*/
	
    if (xml) dumpAsXML(f, pageNum);
		/*outfile << "Dump1"<<std::endl;
	outfile.close();*/
    if (!xml) dumpComplex(f, pageNum);  
 /* }
  else
  {*/
   /* fprintf(f,"<a name=%d></a>",pageNum);
    GString* fName=basename(DocName); 
    for (int i=1;i<HtmlOutputDev::imgNum;i++)
      fprintf(f,"<img src=\"%s-%d_%d.jpg\"><br>\n",fName->getCString(),pageNum,i);
    HtmlOutputDev::imgNum=1;
    delete fName;

    GString* str;
    for(HtmlString *tmp=yxStrings;tmp;tmp=tmp->yxNext){
      if (tmp->htext){
		str=new GString(tmp->htext); 
		fputs(str->getCString(),f);
		delete str;      
		fputs("<br>\n",f);  
      }*/
   /* }*/
	//fputs("<hr>\n",f);  
 // }
}



void HtmlPage::clear() {
  HtmlString *p1, *p2;

  if (curStr) {
    delete curStr;
    curStr = NULL;
  }
  for (p1 = yxStrings; p1; p1 = p2) {
    p2 = p1->yxNext;
    delete p1;
  }
  yxStrings = NULL;
  xyStrings = NULL;
  yxCur1 = yxCur2 = NULL;

  if( !noframes )
  {
      delete fonts;
      fonts=new HtmlFontAccu();
      fontsPageMarker = 0;
	  paragraphPageMarker=0;
  }
  else
  {
      fontsPageMarker = fonts->size();	 
  }

  delete links;
  links=new HtmlLinks();
 

}

void HtmlPage::setDocName(char *fname){
  DocName=new GString(fname);
}

void HtmlPage::updateCharSpace(GfxState *state)
{
	charspace = state->getCharSpace();
}

//------------------------------------------------------------------------
// HtmlMetaVar
//------------------------------------------------------------------------

HtmlMetaVar::HtmlMetaVar(char *_name, char *_content)
{
    name = new GString(_name);
    content = new GString(_content);
}

HtmlMetaVar::~HtmlMetaVar()
{
   delete name;
   delete content;
} 
    
GString* HtmlMetaVar::toString()	
{
    GString *result = new GString("<meta name=\"");
    result->append(name);
    result->append("\" content=\"");
    result->append(content);
    result->append("\">"); 
    return result;
}

//------------------------------------------------------------------------
// HtmlOutputDev
//------------------------------------------------------------------------

static char* HtmlEncodings[][2] = {
    {"Latin1", "ISO-8859-1"},
    {NULL, NULL}
};


char* HtmlOutputDev::mapEncodingToHtml(GString* encoding)
{
    char* enc = encoding->getCString();
    for(int i = 0; HtmlEncodings[i][0] != NULL; i++)
    {
	if( strcmp(enc, HtmlEncodings[i][0]) == 0 )
	{
	    return HtmlEncodings[i][1];
	}
    }
    return enc; 
}

void HtmlOutputDev::doFrame(int firstPage){
  GString* fName=new GString(Docname);
  char* htmlEncoding;
  fName->append(".html");

  if (!(fContentsFrame = fopen(fName->getCString(), "w"))){
    delete fName;
    error(-1, "Couldn't open html file '%s'", fName->getCString());
    return;
  }
  
  delete fName;
    
  fName=basename(Docname);
  fputs(DOCTYPE_FRAMES, fContentsFrame);
  fputs("\n<html>",fContentsFrame);
  fputs("\n<head>",fContentsFrame);
  fprintf(fContentsFrame,"\n<title>%s</title>",docTitle->getCString());
  htmlEncoding = mapEncodingToHtml(globalParams->getTextEncodingName());
  fprintf(fContentsFrame, "\n<meta http-equiv=\"Content-Type\" content=\"text/html; charset=%s\">\n", htmlEncoding);
  dumpMetaVars(fContentsFrame);
  fprintf(fContentsFrame, "</head>\n");
  fputs("<frameset cols=\"100,*\">\n",fContentsFrame);
  fprintf(fContentsFrame,"<FRAME name=\"links\" src=\"%s_ind.html\">\n",fName->getCString());
  fputs("<frame name=\"contents\" src=",fContentsFrame); 
  if (complexMode) 
      fprintf(fContentsFrame,"\"%s-%d.html\"",fName->getCString(), firstPage);
  else
      fprintf(fContentsFrame,"\"%ss.html\"",fName->getCString());
  
  fputs(">\n</frameset>\n</html>\n",fContentsFrame);
 
  delete fName;
  fclose(fContentsFrame);  
}

HtmlOutputDev::HtmlOutputDev(char *fileName, char *title, 
	char *author, char *keywords, char *subject, char *date,
	char *extension,
	GBool rawOrder, int firstPage, GBool outline, double escala, int jpegQuality) 
{
  this->jpegQuality = jpegQuality;

  char *htmlEncoding;
  scale = escala;
  splash = new SplashOutputDev(splashModeRGB8, 1, gFalse, splash_white, gTrue, gTrue);
  splash->startDoc(this->xref);

  fContentsFrame = NULL;
  docTitle = new GString(title);
  pages = NULL;
  dumpJPEG=gTrue;
  //write = gTrue;
  this->rawOrder = rawOrder;
  this->doOutline = outline;
  ok = gFalse;
  imgNum=1;
  //this->firstPage = firstPage;
  //pageNum=firstPage;
  // open file
  needClose = gFalse;
  pages = new HtmlPage(rawOrder, extension);
  
  glMetaVars = new GList();
  glMetaVars->append(new HtmlMetaVar("generator", "pdftohtml 0.40"));  
  if( author ) glMetaVars->append(new HtmlMetaVar("author", author));  
  if( keywords ) glMetaVars->append(new HtmlMetaVar("keywords", keywords));  
  if( date ) glMetaVars->append(new HtmlMetaVar("date", date));  
  if( subject ) glMetaVars->append(new HtmlMetaVar("subject", subject));
 
  maxPageWidth = 0;
  maxPageHeight = 0;

  pages->setDocName(fileName);
  Docname=new GString (fileName);

  // for non-xml output (complex or simple) with frames generate the left frame
  if(!xml && !noframes)
  {
     GString* left=new GString(fileName);
     left->append("_ind.html");

     doFrame(firstPage);
   
     if (!(fContentsFrame = fopen(left->getCString(), "w")))
	 {
        error(-1, "Couldn't open html file '%s'", left->getCString());
		delete left;
        return;
     }
     delete left;
     fputs(DOCTYPE, fContentsFrame);
     fputs("<html>\n<head>\n<title></title>\n</head>\n<body>\n",fContentsFrame);
     
  	if (doOutline)
	{
		GString *str = basename(Docname);
		fprintf(fContentsFrame, "<a href=\"%s%s\" target=\"contents\">Outline</a><br>", str->getCString(), complexMode ? "-outline.html" : "s.html#outline");
		delete str;
	}
  	
	if (!complexMode)
	{	/* not in complex mode */
		
       GString* right=new GString(fileName);
       right->append("s.html");

       if (!(page=fopen(right->getCString(),"w"))){
        error(-1, "Couldn't open html file '%s'", right->getCString());
        delete right;
		return;
       }
       delete right;
       fputs(DOCTYPE, page);
       fputs("<html>\n<head>\n<title></TITLE>\n</head>\n<body>\n",page);
     }
  }

  if (noframes) {
    if (stout) page=stdout;
    else {
      GString* right=new GString(fileName);
      if (!xml) right->append(".html");
      if (xml) right->append(".xml");
      if (!(page=fopen(right->getCString(),"w"))){
	delete right;
	error(-1, "Couldn't open html file '%s'", right->getCString());
	return;
      }  
      delete right;
    }

    htmlEncoding = mapEncodingToHtml(globalParams->getTextEncodingName()); 
    if (xml) 
    {
      fprintf(page, "<?xml version=\"1.0\" encoding=\"%s\"?>\n", htmlEncoding);
      fputs("<!DOCTYPE pdf2xml SYSTEM \"pdf2xml.dtd\">\n\n", page);
      fputs("<pdf2xml>\n",page);
    } 
    else 
    {
      fprintf(page,"%s\n<html>\n<head>\n<title>%s</title>\n",
	      DOCTYPE, docTitle->getCString());
      
      fprintf(page, "<meta http-equiv=\"Content-Type\" content=\"text/html; charset=%s\">\n", htmlEncoding);
      
      dumpMetaVars(page);
      fprintf(page,"</head>\n");
      fprintf(page,"<body bgcolor=\"#FFFFFF\" vlink=\"blue\" link=\"blue\">\n");
    }
  }
  ok = gTrue; 
}

HtmlOutputDev::~HtmlOutputDev() {
  /*if (mode&&!xml){
    int h=xoutRound(pages->pageHeight/scale);
    int w=xoutRound(pages->pageWidth/scale);
    fprintf(tin,"%s=%03d\n","PAPER_WIDTH",w);
    fprintf(tin,"%s=%03d\n","PAPER_HEIGHT",h);
    fclose(tin);
    }*/

    HtmlFont::clear(); 

    delete Docname;
    delete docTitle;

    deleteGList(glMetaVars, HtmlMetaVar);

    if (fContentsFrame){
      fputs("</body>\n</html>\n",fContentsFrame);  
      fclose(fContentsFrame);
    }
    if (xml) {
      fputs("</pdf2xml>\n",page);  
      fclose(page);
    } else
    if ( !complexMode || xml || noframes )
    { 
      fputs("</body>\n</html>\n",page);  
      fclose(page);
    }
    if (pages)
      delete pages;

	delete splash;
}



void HtmlOutputDev::startPage(int pageNum, GfxState *state, double x1,double y1,double x2,double y2) {
	splash->startPage(pageNum, state, x1, y1, x2, y2);
	return startPage(pageNum, state);
}

void HtmlOutputDev::startPage(int pageNum, GfxState *state) {
  /*if (mode&&!xml){
    if (write){
      write=gFalse;
      GString* fname=Dirname(Docname);
      fname->append("image.log");
      if((tin=fopen(fname->getCString(),"w"))==NULL){
	printf("Error : can not open %s",fname);
	exit(1);
      }
      delete fname;
    // if(state->getRotation()!=0) 
    //  fprintf(tin,"ROTATE=%d rotate %d neg %d neg translate\n",state->getRotation(),state->getX1(),-state->getY1());
    // else 
      fprintf(tin,"ROTATE=%d neg %d neg translate\n",state->getX1(),state->getY1());  
    }
  }*/

  this->pageNum = pageNum;
  GString *str=basename(Docname);
  pages->clear(); 
  if(!noframes)
  {
    if (fContentsFrame)
	{
     // if (complexMode)
		fprintf(fContentsFrame,"<a href=\"%s-%d.html\"",str->getCString(),pageNum);
     /* else 
		fprintf(fContentsFrame,"<a href=\"%ss.html#%d\"",str->getCString(),pageNum);*/
      fprintf(fContentsFrame," target=\"contents\" >Page %d</a><br>\n",pageNum);
    }
  }

  pages->pageWidth=static_cast<int>(state->getPageWidth());
  pages->pageHeight=static_cast<int>(state->getPageHeight());

  delete str;
} 

typedef struct _gfxcolor
{
    unsigned char a;
    unsigned char r;
    unsigned char g;
    unsigned char b;
} gfxcolor_t;


void writeMonoBitmap(SplashBitmap*btm, char*filename, char *ext, int jpegQuality)
{
    int width8 = (btm->getWidth()+7)/8;
    int width = btm->getWidth();
    int height = btm->getHeight();
    gfxcolor_t*b = (gfxcolor_t*)malloc(sizeof(gfxcolor_t)*width*height);
    unsigned char*data = btm->getDataPtr();
    int x,y;
    for(y=0;y<height;y++) {
        unsigned char*l = &data[width8*y];
        gfxcolor_t*d = &b[width*y];
        for(x=0;x<width;x++) {
            if(l[x>>3]&(128>>(x&7))) {
                d[x].r = d[x].b = d[x].a = 255;
		d[x].g = 0;
            } else {
                d[x].r = d[x].g = d[x].b = d[x].a = 0;
            }
        }
    }
	if(ext == "png")
		writePNG(filename, (unsigned char*)b, width, height);
	else
		jpeg_save((unsigned char*)b, width, height, jpegQuality, filename);
    free(b);
}

void HtmlOutputDev::endPage() {
  pages->conv();
  pages->coalesce();
 /* std::ofstream outfile ("endpage.txt");
	outfile << "endpage"<<std::endl;
	outfile.close();*/
  pages->dump(page, pageNum);
  
	char fileName[1024];
	char *ext = pages->getImageExt()->getCString();
	//ext = 
	sprintf(fileName,"%s%03d.%s", pages->getDocName()->getCString(), pageNum, ext);

	if(jpegQuality < 0 || jpegQuality > 100)
		jpegQuality = 85;

	int y,x;
    SplashBitmap *bitmap = splash->getBitmap();
    int width = splash->getBitmapWidth();
    int height = splash->getBitmapHeight();

    

    if(bitmap->getMode()==splashModeMono1) {
        writeMonoBitmap(bitmap, fileName, pages->getImageExt()->getCString(), jpegQuality);
        return;
    }

	if(!strcmp(ext,"png"))
	{
		gfxcolor_t*data = (gfxcolor_t*)malloc(sizeof(gfxcolor_t)*width*height);
		for(y=0;y<height;y++) {
			gfxcolor_t*line = &data[y*width];
			for(x=0;x<width;x++) 
			{
				Guchar c[4] = {0,0,0,0};
				bitmap->getPixel(x,y,c);
				line[x].r = c[0];
				line[x].g = c[1];
				line[x].b = c[2];
				line[x].a = (unsigned char)  bitmap->getAlpha(x,y);
			}
		}
		writePNG(fileName, (unsigned char*)data, width, height);
		free(data);
	}
	else if(!strcmp(ext, "jpg") || !strcmp(ext, "jpeg"))
	{
		/*unsigned char * data = (unsigned char*)malloc(3*width*height);

		for(y=0;y<height;y++) {
			unsigned char*line = &data[y*width];
			for(x=0;x<width;x++) 
			{
				Guchar c[4] = {0,0,0,0};
				bitmap->getPixel(x,y,c);
				line[0] = (unsigned char)c[0];
				line[1] = (unsigned char)c[1];
				line[2] = (unsigned char)c[2];
				line+=3;
			}
		}*/
		//JpegFromDib
		jpeg_save((unsigned char*)bitmap->getDataPtr(), width, height, jpegQuality, fileName);
//		free(data);
	}

  // I don't yet know what to do in the case when there are pages of different
  // sizes and we want complex output: running ghostscript many times 
  // seems very inefficient. So for now I'll just use last page's size
  maxPageWidth = pages->pageWidth;
  maxPageHeight = pages->pageHeight;
  
  //if(!noframes&&!xml) fputs("<br>\n", fContentsFrame);
  if(!stout && !globalParams->getErrQuiet()) printf("Page-%d\n",(pageNum));
}

void HtmlOutputDev::updateFont(GfxState *state) {
  pages->updateFont(state);
}

void HtmlOutputDev::beginString(GfxState *state, GString *s) {
  pages->beginString(state, s);
}

void HtmlOutputDev::endString(GfxState *state) {
  pages->endString();
}

void HtmlOutputDev::drawChar(GfxState *state, double x, double y,
	      double dx, double dy,
	      double originX, double originY,
	      CharCode code, int nBytes, Unicode *u, int uLen) 
{
  if ( !showHidden && (state->getRender() & 3) == 3) {
    return;
  }
  pages->addChar(state, x, y, dx, dy, originX, originY, u, uLen);
}

void HtmlOutputDev::drawImageMask(GfxState *state, Object *ref, Stream *str,
			      int width, int height, GBool invert,
			      GBool inlineImg) {

  int i, j;
  
  if (ignore||complexMode) {
	  splash->drawImageMask(state, ref, str, width, height, invert, inlineImg);
    return;
  }
  
  FILE *f1;
  int c;
  
  int x0, y0;			// top left corner of image
  int w0, h0, w1, h1;		// size of image
  double xt, yt, wt, ht;
  GBool rotate, xFlip, yFlip;
  GBool dither;
  int x, y;
  int ix, iy;
  int px1, px2, qx, dx;
  int py1, py2, qy, dy;
  Gulong pixel;
  int nComps, nVals, nBits;
  double r1, g1, b1;
 
  // get image position and size
  state->transform(0, 0, &xt, &yt);
  state->transformDelta(1, 1, &wt, &ht);
  if (wt > 0) {
    x0 = xoutRound(xt);
    w0 = xoutRound(wt);
  } else {
    x0 = xoutRound(xt + wt);
    w0 = xoutRound(-wt);
  }
  if (ht > 0) {
    y0 = xoutRound(yt);
    h0 = xoutRound(ht);
  } else {
    y0 = xoutRound(yt + ht);
    h0 = xoutRound(-ht);
  }
  state->transformDelta(1, 0, &xt, &yt);
  rotate = fabs(xt) < fabs(yt);
  if (rotate) {
    w1 = h0;
    h1 = w0;
    xFlip = ht < 0;
    yFlip = wt > 0;
  } else {
    w1 = w0;
    h1 = h0;
    xFlip = wt < 0;
    yFlip = ht > 0;
  }

  // dump JPEG file
  if (dumpJPEG  && str->getKind() == strDCT) {
    GString *fName=new GString(Docname);
    fName->append("-");
    GString *pgNum=GString::fromInt(pageNum);
    GString *imgnum=GString::fromInt(imgNum);
    // open the image file
    fName->append(pgNum)->append("_")->append(imgnum)->append(".jpg");
    ++imgNum;
    if (!(f1 = fopen(fName->getCString(), "wb"))) {
      error(-1, "Couldn't open image file '%s'", fName->getCString());
      return;
    }

    // initialize stream
    str = ((DCTStream *)str)->getRawStream();
    str->reset();

    // copy the stream
    while ((c = str->getChar()) != EOF)
      fputc(c, f1);

    fclose(f1);
   
  if (pgNum) delete pgNum;
  if (imgnum) delete imgnum;
  if (fName) delete fName;
  }
  else {

    OutputDev::drawImageMask(state, ref, str, width, height, invert, inlineImg);
  }
}

void HtmlOutputDev::drawImage(GfxState *state, Object *ref, Stream *str,
			  int width, int height, GfxImageColorMap *colorMap,
			  int *maskColors, GBool inlineImg) {

  int i, j;
   
// if (ignore||complexMode) {
	  splash->drawImage(state, ref, str, width, height, colorMap, 
			 maskColors, inlineImg);
  /*  return;
  }*/

  FILE *f1;
  ImageStream *imgStr;
  Guchar pixBuf[4];
  GfxColor color;
  int c;
  
  int x0, y0;			// top left corner of image
  int w0, h0, w1, h1;		// size of image
  double xt, yt, wt, ht;
  GBool rotate, xFlip, yFlip;
  GBool dither;
  int x, y;
  int ix, iy;
  int px1, px2, qx, dx;
  int py1, py2, qy, dy;
  Gulong pixel;
  int nComps, nVals, nBits;
  double r1, g1, b1;
 
  // get image position and size
  state->transform(0, 0, &xt, &yt);
  state->transformDelta(1, 1, &wt, &ht);
  if (wt > 0) {
    x0 = xoutRound(xt);
    w0 = xoutRound(wt);
  } else {
    x0 = xoutRound(xt + wt);
    w0 = xoutRound(-wt);
  }
  if (ht > 0) {
    y0 = xoutRound(yt);
    h0 = xoutRound(ht);
  } else {
    y0 = xoutRound(yt + ht);
    h0 = xoutRound(-ht);
  }
  state->transformDelta(1, 0, &xt, &yt);
  rotate = fabs(xt) < fabs(yt);
  if (rotate) {
    w1 = h0;
    h1 = w0;
    xFlip = ht < 0;
    yFlip = wt > 0;
  } else {
    w1 = w0;
    h1 = h0;
    xFlip = wt < 0;
    yFlip = ht > 0;
  }

   
  /*if( !globalParams->getErrQuiet() )
    printf("image stream of kind %d\n", str->getKind());*/
  // dump JPEG file
  if (dumpJPEG && str->getKind() == strDCT) {
    GString *fName=new GString(Docname);
    fName->append("-");
    GString *pgNum= GString::fromInt(pageNum);
    GString *imgnum= GString::fromInt(imgNum);  
    
    // open the image file
    fName->append(pgNum)->append("_")->append(imgnum)->append(".jpg");
    ++imgNum;
    
    if (!(f1 = fopen(fName->getCString(), "wb"))) {
      error(-1, "Couldn't open image file '%s'", fName->getCString());
      return;
    }

    // initialize stream
    str = ((DCTStream *)str)->getRawStream();
    str->reset();

    // copy the stream
    while ((c = str->getChar()) != EOF)
      fputc(c, f1);
    
    fclose(f1);
  
    delete fName;
    delete pgNum;
    delete imgnum;
  }
  else {
    OutputDev::drawImage(state, ref, str, width, height, colorMap,
			 maskColors, inlineImg);
  }
}



void HtmlOutputDev::drawLink(Link* link,Catalog *cat){
  double _x1,_y1,_x2,_y2,w;
  int x1,y1,x2,y2;
  w = 1;

  link->getRect(&_x1,&_y1,&_x2,&_y2);
  cvtUserToDev(_x1,_y1,&x1,&y1);
  
  cvtUserToDev(_x2,_y2,&x2,&y2); 


  GString* _dest=getLinkDest(link,cat);
  HtmlLink t((double) x1,(double) y2,(double) x2,(double) y1,_dest);
  pages->AddLink(t);
  delete _dest;
}

GString* HtmlOutputDev::getLinkDest(Link *link,Catalog* catalog){
  char *p;
  switch(link->getAction()->getKind()) 
  {
      case actionGoTo:
	  { 
	  GString* file=basename(Docname);
	  int page=1;
	  LinkGoTo *ha=(LinkGoTo *)link->getAction();
	  LinkDest *dest=NULL;
	  if (ha->getDest()==NULL) 
	      dest=catalog->findDest(ha->getNamedDest());
	  else 
	      dest=ha->getDest()->copy();
	  if (dest){ 
	      if (dest->isPageRef()){
		  Ref pageref=dest->getPageRef();
		  page=catalog->findPage(pageref.num,pageref.gen);
	      }
	      else {
		  page=dest->getPageNum();
	      }

	      delete dest;

	      GString *str=GString::fromInt(page);
	      /* 		complex 	simple
	       	frames		file-4.html	files.html#4
		noframes	file.html#4	file.html#4
	       */
	      if (noframes)
	      {
		  file->append(".html#");
		  file->append(str);
	      }
	      else
	      {
	      	if( complexMode ) 
		{
		    file->append("-");
		    file->append(str);
		    file->append(".html");
		}
		else
		{
		    file->append("s.html#");
		    file->append(str);
		}
	      }

	      if (printCommands) printf(" link to page %d ",page);
	      delete str;
	      return file;
	  }
	  else 
	  {
	      return new GString();
	  }
	  }
      case actionGoToR:
	  {
	  LinkGoToR *ha=(LinkGoToR *) link->getAction();
	  LinkDest *dest=NULL;
	  int page=1;
	  GString *file=new GString();
	  if (ha->getFileName()){
	      delete file;
	      file=new GString(ha->getFileName()->getCString());
	  }
	  if (ha->getDest()!=NULL)  dest=ha->getDest()->copy();
	  if (dest&&file){
	      if (!(dest->isPageRef()))  page=dest->getPageNum();
	      delete dest;

	      if (printCommands) printf(" link to page %d ",page);
	      if (printHtml){
		  p=file->getCString()+file->getLength()-4;
		  if (!strcmp(p, ".pdf") || !strcmp(p, ".PDF")){
		      file->del(file->getLength()-4,4);
		      file->append(".html");
		  }
		  file->append('#');
		  file->append(GString::fromInt(page));
	      }
	  }
	  if (printCommands) printf("filename %s\n",file->getCString());
	  return file;
	  }
      case actionURI:
	  { 
	  LinkURI *ha=(LinkURI *) link->getAction();
	  GString* file=new GString(ha->getURI()->getCString());
	  // printf("uri : %s\n",file->getCString());
	  return file;
	  }
      case actionLaunch:
	  {
	  LinkLaunch *ha=(LinkLaunch *) link->getAction();
	  GString* file=new GString(ha->getFileName()->getCString());
	  if (printHtml) { 
	      p=file->getCString()+file->getLength()-4;
	      if (!strcmp(p, ".pdf") || !strcmp(p, ".PDF")){
		  file->del(file->getLength()-4,4);
		  file->append(".html");
	      }
	      if (printCommands) printf("filename %s",file->getCString());
    
	      return file;      
  
	  }
	  }
      default:
	  return new GString();
  }
}

void HtmlOutputDev::dumpMetaVars(FILE *file)
{
  GString *var;

  for(int i = 0; i < glMetaVars->getLength(); i++)
  {
     HtmlMetaVar *t = (HtmlMetaVar*)glMetaVars->get(i); 
     var = t->toString(); 
     fprintf(file, "%s\n", var->getCString());
     delete var;
  }
}

GBool HtmlOutputDev::dumpDocOutline(Catalog* catalog)
{ 
	FILE * output;
	GBool bClose = gFalse;

	if (!ok || xml)
    	return gFalse;
  
	Object *outlines = catalog->getOutline();
	
  	//if (!outlines->isDict())
    	return gFalse;
  
	if (!complexMode && !xml)
  	{
		output = page;
  	}
  	else if (complexMode && !xml)
	{
		if (noframes)
		{
			output = page; 
			fputs("<hr>\n", output);
		}
		else
		{
			GString *str = basename(Docname);
			str->append("-outline.html");
			output = fopen(str->getCString(), "w");
			if (output == NULL)
				return gFalse;
			delete str;
			bClose = gTrue;
     		fputs("<html>\n<head>\n<title>Document Outline</title>\n</head>\n<body>\n", output);
		}
	}
 
  	GBool done = newOutlineLevel(output, outlines, catalog);
  	if (done && !complexMode)
    	fputs("<hr>\n", output);
	
	if (bClose)
	{
		fputs("</body>\n</html>\n", output);
		fclose(output);
	}
  	return done;
}

GBool HtmlOutputDev::newOutlineLevel(FILE *output, Object *node, Catalog* catalog, int level)
{
  Object curr, next;
  GBool atLeastOne = gFalse;
  
  if (node->dictLookup("First", &curr)->isDict()) {
    if (level == 1)
	{
		fputs("<A name=\"outline\"></a>", output);
		fputs("<h1>Document Outline</h1>\n", output);
	}
    fputs("<ul>",output);
    do {
      // get title, give up if not found
      Object title;
      if (curr.dictLookup("Title", &title)->isNull()) {
		title.free();
		break;
      }
      GString *titleStr = new GString(title.getString());
      title.free();

      // get corresponding link
      // Note: some code duplicated from HtmlOutputDev::getLinkDest().
      GString *linkName = NULL;;
      Object dest;
      if (!curr.dictLookup("Dest", &dest)->isNull()) {
		LinkGoTo *link = new LinkGoTo(&dest);
		LinkDest *linkdest=NULL;
		if (link->getDest()==NULL) 
	  		linkdest=catalog->findDest(link->getNamedDest());
		else 
	  		linkdest=link->getDest()->copy();
		delete link;
		if (linkdest) { 
	  		int page;
	  		if (linkdest->isPageRef()) {
	    		Ref pageref=linkdest->getPageRef();
	    		page=catalog->findPage(pageref.num,pageref.gen);
	  		} else {
	    		page=linkdest->getPageNum();
	  		}
	  		delete linkdest;

			/* 			complex 	simple
			frames		file-4.html	files.html#4
			noframes	file.html#4	file.html#4
	   		*/
	  		linkName=basename(Docname);
	  		GString *str=GString::fromInt(page);
	  		if (noframes) {
	    		linkName->append(".html#");
				linkName->append(str);
	  		} else {
    			if( complexMode ) {
	   		   		linkName->append("-");
	      			linkName->append(str);
	      			linkName->append(".html");
	    		} else {
	      			linkName->append("s.html#");
	      			linkName->append(str);
	    		}
	  		}
			delete str;
		}
      }
      dest.free();

      fputs("<li>",output);
      if (linkName)
		fprintf(output,"<a href=\"%s\">", linkName->getCString());
      fputs(titleStr->getCString(),output);
      if (linkName) {
		fputs("</a>",output);
		delete linkName;
      }
      fputs("\n",output);
      delete titleStr;
      atLeastOne = gTrue;

      newOutlineLevel(output, &curr, catalog, level+1);
      curr.dictLookup("Next", &next);
      curr.free();
      curr = next;
    } while(curr.isDict());
    fputs("</ul>",output);
  }
  curr.free();

  return atLeastOne;
}

void HtmlOutputDev::updateCharSpace(GfxState *state)
{
	pages->updateCharSpace(state);
}

void HtmlOutputDev::drawMaskedImage(GfxState *state, Object *ref, Stream *str,
			       int width, int height,
			       GfxImageColorMap *colorMap,
			       Stream *maskStr, int maskWidth, int maskHeight,
			       GBool maskInvert)
{
	splash->drawMaskedImage(state, ref, str, width, height, colorMap, maskStr, maskWidth, maskHeight, maskInvert);
}
void HtmlOutputDev::drawSoftMaskedImage(GfxState *state, Object *ref, Stream *str,
				   int width, int height,
				   GfxImageColorMap *colorMap,
				   Stream *maskStr,
				   int maskWidth, int maskHeight,
				   GfxImageColorMap *maskColorMap)
{
	splash->drawSoftMaskedImage(state, ref, str, width, height, colorMap, maskStr, maskWidth, maskHeight, maskColorMap);
}

void HtmlOutputDev::saveState(GfxState *state)
{
	splash->saveState(state);
}
void HtmlOutputDev::restoreState(GfxState *state)
{
	splash->restoreState(state);
}

void HtmlOutputDev::updateAll(GfxState *state)
{
	splash->updateAll(state);
}
void HtmlOutputDev::updateCTM(GfxState *state, double m11, double m12, double m21, double m22, double m31, double m32)
{
	splash->updateCTM(state, m11, m12, m21, m22, m31, m32);
}
void HtmlOutputDev::updateLineDash(GfxState *state)
{
	splash->updateLineDash(state);
}
void HtmlOutputDev::updateFlatness(GfxState *state)
{
	splash->updateFlatness(state);
}
void HtmlOutputDev::updateLineJoin(GfxState *state)
{
	splash->updateLineJoin(state);
}
void HtmlOutputDev::updateLineCap(GfxState *state){ splash->updateLineCap(state); }
void HtmlOutputDev::updateMiterLimit(GfxState *state){ splash->updateMiterLimit(state); }
void HtmlOutputDev::updateLineWidth(GfxState *state){ splash->updateLineWidth(state); }
void HtmlOutputDev::updateStrokeAdjust(GfxState *state){ splash->updateStrokeAdjust(state); }
void HtmlOutputDev::updateFillColorSpace(GfxState *state){ splash->updateFillColorSpace(state); }
void HtmlOutputDev::updateStrokeColorSpace(GfxState *state){ splash->updateStrokeColorSpace(state); }
void HtmlOutputDev::updateFillColor(GfxState *state){ splash->updateFillColor(state); }
void HtmlOutputDev::updateStrokeColor(GfxState *state){ splash->updateStrokeColor(state); }
void HtmlOutputDev::updateBlendMode(GfxState *state){ splash->updateBlendMode(state); }
void HtmlOutputDev::updateFillOpacity(GfxState *state){ splash->updateFillOpacity(state); }
void HtmlOutputDev::updateStrokeOpacity(GfxState *state){ splash->updateStrokeOpacity(state); }
void HtmlOutputDev::updateFillOverprint(GfxState *state){ splash->updateFillOverprint(state); }
void HtmlOutputDev::updateStrokeOverprint(GfxState *state){ splash->updateStrokeOverprint(state);}
void HtmlOutputDev::updateTransfer(GfxState *state){ splash->updateTransfer(state); }
void HtmlOutputDev::updateTextMat(GfxState *state){ splash->updateTextMat(state); }
void HtmlOutputDev::updateRender(GfxState *state){ splash->updateRender(state); }
void HtmlOutputDev::updateRise(GfxState *state){ splash->updateRise(state); }
void HtmlOutputDev::updateWordSpace(GfxState *state){ splash->updateWordSpace(state); }
void HtmlOutputDev::updateHorizScaling(GfxState *state){ splash->updateHorizScaling(state); }
void HtmlOutputDev::updateTextPos(GfxState *state){ splash->updateTextPos(state); }
void HtmlOutputDev::updateTextShift(GfxState *state, double shift){ splash->updateTextShift(state, shift); }

void HtmlOutputDev::stroke(GfxState *state){ splash->stroke(state); }
void HtmlOutputDev::fill(GfxState *state){ splash->fill(state); }
void HtmlOutputDev::eoFill(GfxState *state){ splash->eoFill(state); }

void HtmlOutputDev::tilingPatternFill(GfxState *state, Object *str, int paintType, Dict *resDict, double *mat, double *bbox, int x0, int y0, int x1, int y1, double xStep, double yStep){ splash->tilingPatternFill(state, str, paintType, resDict, mat, bbox, x0,y0,x1,y1,xStep,yStep); }
GBool HtmlOutputDev::functionShadedFill(GfxState *state, GfxFunctionShading *shading){ return splash->functionShadedFill(state, shading); }
GBool HtmlOutputDev::axialShadedFill(GfxState *state, GfxAxialShading *shading){ return splash->axialShadedFill(state, shading); }
GBool HtmlOutputDev::radialShadedFill(GfxState *state, GfxRadialShading *shading){ return splash->radialShadedFill(state, shading); }

void HtmlOutputDev::clip(GfxState *state){ splash->clip(state); }
void HtmlOutputDev::eoClip(GfxState *state){ splash->eoClip(state); }
void HtmlOutputDev::clipToStrokePath(GfxState *state){ splash->clipToStrokePath(state); }
