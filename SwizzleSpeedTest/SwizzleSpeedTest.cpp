// SwizzleSpeedTest.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <chrono>
#include <iostream>
#include <memory>

using namespace std;

typedef uint32_t u32;
typedef uint16_t u16;
typedef uint8_t u8;

u32 linear_to_swizzle(u32 x, u32 y, u32 z, u32 log2_width, u32 log2_height, u32 log2_depth)
{
    u32 offset = 0;
    u32 shift_count = 0;
    while (log2_width | log2_height | log2_depth)
    {
        if (log2_width)
        {
            offset |= (x & 0x01) << shift_count;
            x >>= 1;
            ++shift_count;
            --log2_width;
        }

        if (log2_height)
        {
            offset |= (y & 0x01) << shift_count;
            y >>= 1;
            ++shift_count;
            --log2_height;
        }

        if (log2_depth)
        {
            offset |= (z & 0x01) << shift_count;
            z >>= 1;
            ++shift_count;
            --log2_depth;
        }
    }
    return offset;
}

void slowSwizzle(void* inputPixels, void* outputPixels, u16 width, u16 height, bool swap = false) {

    u16 log2Width = log2(width);
    u16 log2Height = log2(height);
    u32* pixelSrc = (u32*)inputPixels;
    u32* pixelDst = (u32*)outputPixels;

    for (u16 y = 0; y < height; ++y) {
        u32 rowStart = y * width;
        for (u16 x = 0; x < width; ++x) {
            if (swap)
                pixelDst[linear_to_swizzle(x, y, 0, log2Width, log2Height, 0)] = pixelSrc[rowStart + x];
            else 
                pixelDst[rowStart + x] = pixelSrc[linear_to_swizzle(x, y, 0, log2Width, log2Height, 0)];
        }
    }
}

void fastSwizzle(void* inputPixels, void* outputPixels, u16 width, u16 height, bool swap = false) {
    u32 log2width, log2height;

    log2width = log2(width);
    log2height = log2(height);

    // Max mask possible for square texture (should be 2^11, or 22 bits for x and y)
    u32 x_mask = 0x555555;
    u32 y_mask = 0xAAAAAA;
    if (swap) {
        //y_mask = 0x555555;
       // x_mask = 0xAAAAAA;
    }

    // We have to limit the masks to the lower of the two dimensions to allow for non-square textures
    u32 limitMask = (log2width < log2height) ? log2width : log2height;
    // double the limit mask to account for bits in both x and y
    limitMask = 1 << (limitMask << 1);

    //x_mask, bits above limit are 1's for x-carry
    x_mask = (x_mask | ~(limitMask - 1));
    //y_mask. bits above limit are 0'd, as we use a different method for y-carry over
    y_mask = (y_mask & (limitMask - 1));

    u32 offs_y = 0;
    u32 offs_x = 0;
    u32 offs_x0 = 0; //total y-carry offset for x
    u32 y_incr = limitMask;

    u32 *src, *dst;

    if (swap) {
        for (int y = 0; y < height; ++y) {
            src = (u32 *)((u32*)inputPixels + y*width);
            dst = (u32 *)((u32*)outputPixels + offs_y);
            offs_x = offs_x0;
            for (int x = 0; x < width; ++x) {
                dst[offs_x] = src[x];
                offs_x = (offs_x - x_mask) & x_mask;
            }
            offs_y = (offs_y - y_mask) & y_mask;
            if (offs_y == 0) offs_x0 += y_incr;
        }
    }
    else {
        for (int y = 0; y < height; ++y) {
            src = (u32 *)((u32*)inputPixels + offs_y);
            dst = (u32 *)((u32*)outputPixels + y*width);
            offs_x = offs_x0;
            for (int x = 0; x < width; ++x) {
                dst[x] = src[offs_x];
                offs_x = (offs_x - x_mask) & x_mask;
            }
            offs_y = (offs_y - y_mask) & y_mask;
            if (offs_y == 0) offs_x0 += y_incr;
        }
    }
}

int main()
{
    u16 max_h = 128;
    u16 max_w = 128;
    u32 numTimes = 4;

    chrono::time_point<std::chrono::system_clock> start, end;
    chrono::duration<double> durationslow, durationfast;
    durationslow.zero();
    durationfast.zero();

    u32 *linearPixels = new u32[max_w * max_h];

    for (u32 i = 0; i < max_w * max_h; i++)
        linearPixels[i] = i;//std::rand();

    u32 *slowSwizzlePixels = new u32[max_w * max_h];
    u32 *fastSwizzlePixels = new u32[max_w * max_h];

    for (u32 count = 0; count < numTimes; ++count) {
        memset(slowSwizzlePixels, 0xcc, max_w * max_h);
        memset(fastSwizzlePixels, 0xcc, max_w * max_h);

        start = std::chrono::system_clock::now();
        slowSwizzle(linearPixels, slowSwizzlePixels, max_w, max_h);
        end = std::chrono::system_clock::now();
        durationslow += end - start;


        start = std::chrono::system_clock::now();
        fastSwizzle(linearPixels, fastSwizzlePixels, max_w, max_h);
        end = std::chrono::system_clock::now();
        durationfast += end - start;

        if (memcmp(slowSwizzlePixels, fastSwizzlePixels, max_h * max_w) != 0) {
            printf("mismatch!\n");
            int hold;
            cin >> hold;
        }
    }

    delete[] linearPixels;
    delete[] slowSwizzlePixels;
    delete[] fastSwizzlePixels;

    cout << "Slow time: " << durationslow.count() << endl;
    cout << "Fast total time: " << durationfast.count() << endl;
    cout << "\n Slow / Fast Ratio: " << durationslow.count() / durationfast.count() << endl;

    system("PAUSE");

    return 0;
}

