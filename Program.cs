﻿using System.Numerics;
using System.Runtime.InteropServices;
using OpenCL_Secp256k1.OpenCL;
using OpenCL_Secp256k1.OpenCL.Kernels;
using Silk.NET.OpenCL;

// Welcome to programming with OpenCL, lets keep it simple

// Setup OpenCL context, first we select the platform (NVidia, AMD, Intel, Apple, etc.)
Platform? platform = Platform.GetPlatform("*Apple*", DeviceTypes.Gpu);

if (platform is null)
	throw new Exception($"No OpenCL Platform found. Valid choices: {string.Join(", ", Platform.GetPlatforms().Select(p => p.Vendor))}");

// Didn't get an GPU's check if we have other devices
if (platform.Devices.Length == 0)
{
	//platform.DeviceType = DeviceTypes.All;

	// Just throw an error, technically we could switch to a different type, but lets keep it simple
	if (platform.Devices.Length == 0)
		throw new Exception("No OpenCL Devices found (Platform='{platform.Vendor}')");
	else
		throw new Exception($"No OpenCL >>GPU<< Devices found (Platform='{platform.Vendor}'). Valid device type choices: {string.Join(", ", platform.Devices.Select(d => d.DeviceType.ToString()))}");
}

// Just get the first device (technically, we could use multiple devices, but lets keep it simple)
Device device = platform.Devices[0];

// Create our opencl context
nint context = OpenCLSharp.CreateContext(device);

int devices = Utilities.GetContextInfo_Int32(context, ContextInfo.NumDevices);

Console.WriteLine("=========================================================");
Console.WriteLine("Platform Vendor: " + platform.Vendor);
Console.WriteLine("Device Name: " + device.Name);
Console.WriteLine("Device Type: " + device.DeviceType);
Console.WriteLine("Device Global Memory: " + device.GlobalMemory / 1024 / 1024 + "MB");
Console.WriteLine("Computer Units: " + device.WorkGroupSize + " units");
Console.WriteLine("Context Devices: " + devices + " device" + (devices == 1 ? "" : "s"));
Console.WriteLine("=========================================================\n\n");






// Create our opencl command queue
nint command_queue = OpenCLSharp.CreateCommandQueue(context, device);

// Create our kernel (the actual opencl kernel in contained in this KernelBase class)
Secp256k1_Verify kernel = new Secp256k1_Verify(device: device, context: context, command_queue: command_queue);

uint BUFFER_SIZE = 16;

// Create a buffer. In CSharp we have to pin (so it wont move in memory) only then can we get a pointer to our data
byte[] _input = new byte[BUFFER_SIZE];
byte[] _output = new byte[BUFFER_SIZE];

CLBuffer input = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);
CLBuffer output = new CLBuffer(context, MemFlags.AllocHostPtr | MemFlags.ReadWrite, BUFFER_SIZE);

// Setup some test data
long a = 1234567890123456789;
long b = long.MaxValue;

// Add setup data to the input buffer
Array.Copy(BitConverter.GetBytes(a), 0, _input, 8, 8);
Array.Copy(BitConverter.GetBytes(b), 0, _input, 0, 8);

input.Write(command_queue, _input);

// Verify with BitInteger
BigInteger bigA = new BigInteger(a);
BigInteger bigB = new BigInteger(b);
BigInteger big16 = new BigInteger(16);
BigInteger bigResult = (bigA * bigB) + (bigA * bigB) + big16;

// Do the calculation in OpenCL
nint waitEvent = kernel.Run(input, output, 1);

// Wait for the calculation to finish
OpenCLSharp.WaitForEvent(ref waitEvent);

output.Read(command_queue, ref _output);

// Get the result from the output buffer
ReadOnlySpan<byte> result = new ReadOnlySpan<byte>(_output, 0, 16);
BigInteger openCLResult = new BigInteger(result, false, !BitConverter.IsLittleEndian);


string hexStringA = bigA.ToString("X");
Console.WriteLine("\n\nA: " + hexStringA);

string hexStringB = bigB.ToString("X");
Console.WriteLine("B: " + hexStringB + "\n\n");


string hexStringOpenCL = openCLResult.ToString("X");
Console.WriteLine("OpenCL Result: " + hexStringOpenCL);

string hexString = bigResult.ToString("X");
Console.WriteLine("BigInt Result: " + hexString);
