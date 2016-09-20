#ifndef _PDFTOHTML_H_
#define _PDFTOHTML_H_

int mainHtmlExport(int argc, char *argv, int firstPage, int lastPage,char *outputFileName,bool complexmode,bool noFrame,bool ignoreImages, bool outputHiddenText,float zoom,char *ownerPwd,char *userPwd,void *stream, void *pdfDoc);

#endif