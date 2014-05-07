#include <ppu-lv2.h>
#include <ppu-types.h>
#include <stdio.h>
#include <malloc.h>
#include <string.h>
#include <assert.h>
#include <unistd.h>
#include <sysutil/video.h>
#include <rsx/rsx.h>
//#include <io/pad.h> //psl1ght defines padcapabilites wrong
#include "pad.h"

#include "sconsole.h"

typedef struct {
	int height;
	int width;
	uint32_t *ptr;
	// Internal stuff
	uint32_t offset;
} buffer;

gcmContextData *context;
videoResolution res;
int currentBuffer = 0;
buffer *buffers[2];

//example string with \n
char* longString = " _____________\n< FRENS CANIZ >\n -------------\n        \\   ^__^\n         \\  (oo)\\_______\n            (__)\\       )\\/\\\n                ||----w |\n                ||     ||";

void waitFlip() { // Block the PPU thread untill the previous flip operation has finished.
	while(gcmGetFlipStatus() != 0) ;
		usleep(200);
	gcmResetFlipStatus();
}

void flip(s32 buffer)
{
	assert(gcmSetFlip(context, buffer) == 0);
	rsxFlushBuffer(context);
	gcmSetWaitFlip(context);
}

void makeBuffer(int id, int size)
{
	buffer *buf = malloc(sizeof(buffer));
	buf->ptr = rsxMemalign(16, size);
	assert(buf->ptr != NULL);

	assert(rsxAddressToOffset(buf->ptr, &buf->offset) == 0);
	assert(gcmSetDisplayBuffer(id, buf->offset, res.width * 4, res.width, res.height) == 0);
	
	buf->width = res.width;
	buf->height = res.height;
	buffers[id] = buf;
}

void init_screen()
{
	void *host_addr = memalign(1024*1024, 1024*1024);
	assert(host_addr != NULL);

	context = rsxInit(0x10000, 1024*1024, host_addr);
	assert(context != NULL);

	videoState state;
	assert(videoGetState(0, 0, &state) == 0);
	assert(state.state == 0);

	assert(videoGetResolution(state.displayMode.resolution, &res) == 0);
	
	videoConfiguration vconfig;
	memset(&vconfig, 0, sizeof(videoConfiguration));
	vconfig.resolution = state.displayMode.resolution;
	vconfig.format = VIDEO_BUFFER_FORMAT_XRGB;
	vconfig.pitch = res.width * 4;

	assert(videoConfigure(0, &vconfig, NULL, 0) == 0);
	assert(videoGetState(0, 0, &state) == 0); 

	s32 buffer_size = 4 * res.width * res.height;
	
	gcmSetFlipMode(GCM_FLIP_VSYNC);
	makeBuffer(0, buffer_size);
	makeBuffer(1, buffer_size);

	gcmResetFlipStatus();
	flip(1);
}

void setupUsTheBuffer(int theBuffer){
	int i,j;
	for(i = 0; i < res.height; i++)
	{
		for(j = 0; j < res.width; j++)
			buffers[theBuffer]->ptr[i* res.width + j] = FONT_COLOR_WHITE;
	}
	
	//header
	print(170, 10, "Controller Pad Test and Info: ",buffers[theBuffer]->ptr);

	//left aka digital 1
	print(90, 50, "L2: ", buffers[theBuffer]->ptr);
	print(90, 66, "L1: ", buffers[theBuffer]->ptr);

	print(90, 90, "UP: ", buffers[theBuffer]->ptr);
	print(20, 106, "LEFT:          RIGHT: ", buffers[theBuffer]->ptr);
	print(85, 122, "DOWN: ", buffers[theBuffer]->ptr);

	//start n select
	print(195, 90, "SEL: ", buffers[theBuffer]->ptr);
	print(270, 90, "STRT: ", buffers[theBuffer]->ptr);

	//right buttons
	print(370, 50, "R2: ", buffers[theBuffer]->ptr);
	print(370, 66, "R1: ", buffers[theBuffer]->ptr);

	print(370, 90, "TRI: ", buffers[theBuffer]->ptr);
	print(330, 106, "SQR:          CIR: ", buffers[theBuffer]->ptr);
	print(365, 122, "CROSS: ", buffers[theBuffer]->ptr);

	//analog
	print(170, 145, "RHztl: ", buffers[theBuffer]->ptr);
	print(265, 145, "LHztl: ", buffers[theBuffer]->ptr);
	print(170, 161, "RVert: ", buffers[theBuffer]->ptr);
	print(265, 161, "LVert: ", buffers[theBuffer]->ptr);

	//capabilities stuff
	print(10, 206, "Controller Capabilities v1 api-", buffers[theBuffer]->ptr);
	print(20, 222, "PS3 spec(ps button and port light): ", buffers[theBuffer]->ptr);
	print(20, 238, "Pressure Sensitive: ", buffers[theBuffer]->ptr);
	print(20, 254, "Six-axis support: ", buffers[theBuffer]->ptr);
	print(20, 270, "High Precision Stick: ", buffers[theBuffer]->ptr);
	print(20, 286, "Vibration: ", buffers[theBuffer]->ptr);
	
	//status things
	print(10, 340, "Controller status - ", buffers[theBuffer]->ptr);
	print(20, 356, "Num Connected: ", buffers[theBuffer]->ptr);
	print(20, 372, "System Intercept: ", buffers[theBuffer]->ptr);
	print(20, 386, "Currently Reading Port: ", buffers[theBuffer]->ptr);
	print(20, 402, "Port Status: ", buffers[theBuffer]->ptr);
}

s32 main(s32 argc, const char* argv[])
{
	padInfo2 padinfo;
	padData paddata;
	padCapabilityInfo padcapinfo;
	//well shoot, this isnt implemented yet...hardcodes it is :(
	padcapinfo.ps3spec = 0;
	padcapinfo.has_pressure = 0;
	padcapinfo.has_sensors = 0;
	padcapinfo.has_vibrate = 0;
	padcapinfo.has_hps = 0;	

	int i, contnum;
	

	init_screen();
	ioPadInit(7);
	/*
		Init the console: arguments (background color, font color, framebuffer, screen width, screen height)
		sconsoleInit(int bgColor, int fgColor, int screenWidth, int screenHeight)
	*/
	sconsoleInit(FONT_COLOR_WHITE, FONT_COLOR_BLACK, res.width, res.height);
	char ts[1000];
	

	//stupid loop in a loop while we loop, do this only once, otherwise 1fps
	//white background
	//should keep the static text up also....keeps fps up
	setupUsTheBuffer(0);
  	setupUsTheBuffer(1);

	while(1)
	{
		//controller goes 0-255 for range of axis'...er axi?
		ioPadGetInfo2(&padinfo);
		for(i=0; i<MAX_PORT_NUM; i++)
		{
			if(padinfo.port_status[i])
			{
				//yey get the data!
				ioPadGetData(i, &paddata);
				contnum = i;
				//enable this after its working
				ioPadGetCapabilityInfo(i, &padcapinfo);
				//if(paddata.BTN_CROSS)
				//	return 0;
			}
		
		}

	//left aka digital 1
	sprintf(ts, "L3: %d", paddata.BTN_L3);
	print(122, 34, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_L2, paddata.PRE_L2);
	print(122, 50, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_L1, paddata.PRE_L1);
	print(122, 66, ts, buffers[currentBuffer]->ptr);

	sprintf(ts, "%d-%03d", paddata.BTN_UP, paddata.PRE_UP);
	print(122, 90, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_LEFT,paddata.PRE_LEFT);
	print(68, 106, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_RIGHT,paddata.PRE_RIGHT);
	print(196, 106, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_DOWN, paddata.PRE_DOWN);
	print(133, 122, ts, buffers[currentBuffer]->ptr);

	//start n select
	sprintf(ts, "%d", paddata.BTN_SELECT);
	print(235, 90, ts, buffers[currentBuffer]->ptr);

	sprintf(ts, "%d", paddata.BTN_START);
	print(318, 90, ts, buffers[currentBuffer]->ptr);

	//right buttons
	sprintf(ts, "R3: %d", paddata.BTN_R3);
	print(402, 34, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_R2, paddata.PRE_R2);
	print(402, 50, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_R1, paddata.PRE_R1);
	print(402, 66, ts, buffers[currentBuffer]->ptr);

	sprintf(ts, "%d-%03d", paddata.BTN_TRIANGLE, paddata.PRE_TRIANGLE);
	print(410, 90, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_SQUARE,paddata.PRE_SQUARE);
	print(370, 106, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_CIRCLE,paddata.PRE_CIRCLE);
	print(482, 106, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d-%03d", paddata.BTN_CROSS, paddata.PRE_CROSS);
	print(421, 122, ts, buffers[currentBuffer]->ptr);

	//analog
	
	sprintf(ts, "%03d", paddata.ANA_R_H);
	print(226, 145, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%03d", paddata.ANA_L_H);
	print(321, 145, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%03d", paddata.ANA_R_V);
	print(226, 161, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%03d", paddata.ANA_L_V);
	print(321, 161, ts, buffers[currentBuffer]->ptr);

	//capability
	sprintf(ts, "%d", padcapinfo.ps3spec);
	print(308, 222, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", padcapinfo.has_pressure);
	print(180, 238, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", padcapinfo.has_sensors);
	print(164, 254, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", padcapinfo.has_hps);
	print(196, 270, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", padcapinfo.has_vibrate);
	print(108, 286, ts, buffers[currentBuffer]->ptr);

	//status stuff
	sprintf(ts, "%d", padinfo.connected);
	print(140, 356, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", padinfo.info);
	print(164, 372, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "%d", contnum);
	print(212, 386, ts, buffers[currentBuffer]->ptr);
	sprintf(ts, "0x%X", padinfo.port_status[contnum]);
	print(124, 402, ts, buffers[currentBuffer]->ptr);

	//lets try new paddata capabilities	
	sprintf(ts, "PadInfo.v2 capabilites: 0x%X", padinfo.device_capability[contnum]);
	print(20, 418, ts, buffers[currentBuffer]->ptr);

	waitFlip();
	flip(currentBuffer);
	//doOnce(currentBuffer);

	currentBuffer = !currentBuffer;
	}
	
	return 0;
}

