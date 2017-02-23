"use strict"
// TODO:
//  - function to load all of the input values into some object
//  - functions to compute the dimensions of the piece of fabric to cut
//  - how to check that desired dom elements exist?
//  - where to verify input types?

var PatternData;

function GetData()
{
	var width = document.querySelector('#pillow-width').value;
	var height = document.querySelector('#pillow-height').value;
	var seamAllowance = document.querySelector('#pillow-seam-allowance').value;
	var seamStyle = document.querySelector('#pillow-seam-style').value;
	var caseStyle = document.querySelector('#case-style').value;

	// Based on style, will get different things here
	var topFlapWidth = document.querySelector('#pillow-top-flap').value;
	var flapOverlap = document.querySelector('#pillow-flap-overlap').value;
	var flapHemStyle = document.querySelector('#pillow-flap-hem-style').value;
	var flapHemSize = document.querySelector('#pillow-flap-hem-size').value;

	return {
		width: Number(width),
		height: Number(height),
		seamAllowance: Number(seamAllowance),
		seamStyle: seamStyle,
		caseStyle: caseStyle,
		topFlapWidth: Number(topFlapWidth),
		bottomFlapWidth: Number(width) - Number(topFlapWidth) + Number(flapOverlap),
		flapOverlap: Number(flapOverlap),
		flapHemStyle: flapHemStyle,
		flapHemSize: Number(flapHemSize)
	}
}

function pillowFabricWidth()
{
	// TODO: checks on PatternData?

	var leftSeamAllowance = PatternData.seamAllowance;
	var rightSeamAllowance = PatternData.seamAllowance;

	return leftSeamAllowance
			+ 2 * PatternData.width
			+ rightSeamAllowance;
}

function pillowFabricHeight()
{
	// TODO: checks on PatternData?

	var topSeamAllowance = PatternData.seamAllowance;
	var bottomSeamAllowance = PatternData.seamAllowance;

	return topSeamAllowance
			+ PatternData.height
			+ bottomSeamAllowance;
}

function caseFabricWidth()
{
	// TODO: checks on PatternData?

	var hem = 0;

	switch (PatternData.flapHemStyle)
	{
		case "single-fold":
			hem = PatternData.flapHemSize;
			break;
		case "double-fold":
			hem = 2 * PatternData.flapHemSize;
			break;
	}

	return PatternData.width
			+ PatternData.topFlapWidth
			+ PatternData.bottomFlapWidth
			+ 2 * hem;
}

function UpdateOutput()
{
	document.querySelector('#pillow-fabric-width').innerHTML = pillowFabricWidth();
	document.querySelector('#pillow-fabric-height').innerHTML = pillowFabricHeight();
	document.querySelector('#case-fabric-width').innerHTML = caseFabricWidth();
	document.querySelector('#case-fabric-height').innerHTML = pillowFabricHeight();
}

function btn_computePattern_click(e)
{
	PatternData = GetData();

	UpdateOutput();
}

document.onreadystatechange = function(e)
{
    if (document.readyState === 'complete')
    {
    	// load the pattern data with initial values
    	var PatternData = GetData();

    	document.querySelector('#btn_compute-pattern')
    			.addEventListener('click', btn_computePattern_click);
    }
}