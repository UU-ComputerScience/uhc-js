---
layout: default
title: "The Utrecht Haskell Compiler JavaScript Backend"
permalink: /
---
{% capture content %}

## What is UHC-JS?
UHC-JS is the JavaScript backend of the Utrecht Haskell Compiler. It is able of
compiling any Haskell program to JavaScript. This makes it possible to run your
Haskell programs in the browser. Furthermore there is now no more reason for
having to write the verbose language that is called JavaScript yourself. Hurray!

Why do you want to write your web applications in Haskell? Simple, because you
will have access to all goodies that Haskell has to offer, pureness, lazy
evaluation, a compact syntax, an advanced type-system, and access to several
existing libraries that include convenient to use parsers. Haskell offers you
the ability to whip up your own (e)DSL with little effort including any binary
operators you need.

## Resources
For the more academically oriented reader we provide the following reading
materials:


* [Improving the UHC JavaScript Backend](http://www.norm2782.com/improving-uhc-js-report.pdf) - Jurriën Stutterheim
* [Getting Rid of JavaScript with Haskell](http://alessandrovermeulen.me/2012/01/26/getting-rid-of-javascript-with-haskell) - Alessandro Vermeulen
* [The JavaScript Problem (Haskell Wiki)](http://www.haskell.org/haskellwiki/The_JavaScript_Problem#UHC)
* [The UHC Blog](http://utrechthaskellcompiler.wordpress.com/)
* [The UHC Wiki](http://www.cs.uu.nl/wiki/UHC) and [Getting started](http://www.cs.uu.nl/wiki/bin/view/UHC/GettingStarted). 
  Be sure to pick the [js](https://github.com/UU-ComputerScience/uhc/tree/js) branch on the repo for latest developments.
* [UHC JS Backend Quick Start](http://chrisdone.com/posts/2012-01-06-uhc-javascript.html) - Chris Done
* [Client-Side Haskell code](https://github.com/spockz/JCU/tree/master/resources/static/hjs) - Alessandro Vermeulen

## Demo
We have further developed the JCU app as discussed in "Getting Rid of
Javascript with Haskell", it is now JavaScript only and we [put it
online](http://uu-computerscience.github.com/JCU/) for your convenience. No 
account creation is necessary for this version as it stores your data in the
browser locally.

## Need help?
There are currently two major resources for help with UHC. The general [UHC
documentation][uhc-extensive-doc] describes the usage of UHC in general and the
[documentation]({{site.baseurl}}/documentation.html) page providing
documentation for UHC JavaScript specific scenarios.

If you do not reach a solution, please don't hesitate to join the IRC channel
[#uhcjs](irc://irc.freenode.net/uhcjs) on FreeNode.



### Installation
For help installing see [Installation of UHC]({{site.baseurl}}/documentation.html#installation_of_uhc).

### GitHub and Issues
[Our repositories](https://github.com/UU-ComputerScience/) are located at
GitHub. You will find the issue trackers there as well.


[jcu-spockz-fork]: https://github.com/spockz/JCU
[jcu-install-script]: https://gist.github.com/1902090 "A Ruby Script to install JCU and dependencies."
[uhc-github]: https://github.com/UU-ComputerScience
[uhc-js]: https://github.com/UU-ComputerScience/uhc-js
[uhc-extensive-doc]: http://www.cs.uu.nl/wiki/bin/view/Ehc/Documentation

{% endcapture %}

<div class="container">
  <div class="row">
  <div class="span3 bs-docs-sidebar">
    <ul class="nav nav-list bs-docs-sidenav" data-spy="affix"  data-offset-top="80">

          <!-- <li><a href="#getting_started">Getting Started</a></li><li><a href="#communicating_with_javascript">Communicating with JavaScript</a></li><li class="active"><a href="#examples__practice">Examples / Practice</a></li> -->
    </ul>
  </div>
  <div class="span9 content">
    {{ content | markdownify }}
  </div>
  </div>
</div>