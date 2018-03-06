Rsx Vertex data base offset mask test

Expected output on screen is a triangle

This test sets the vertex_data_base register to an 'invalid' value, but when added to the vertex stream offset, and masked, will end up being valid
This helps in figuring out that the rsx internally adds the data_base with the base offsets *before* it translates it into any internal address

R&C games use this functionality of the rsx fairly heavily in their vertex calculations