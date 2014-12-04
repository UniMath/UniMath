/*
 * Copyright(c) 2014, Guillaume Verdier <guillaume@verdier.info>
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 *(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
$(function() {
	$('div.proof').each(function() {
		var html = $(this).html();
		var indent = html.match(/^\s*((?:&nbsp;)*)/)[1];
		var indentsize = indent.length / 6;
		$(this).html(html.replace(new RegExp(indent + "([^&])", 'g'), '$1')).css('margin-left', indentsize + 'ex');
	});
	$('div.code').each(function() {
		var first = $($(this).children()[0]);
		if(first.prop('tagName') === 'A' && first.hasClass('proof')) {
			var prev = $(this).prev();
			if(prev.hasClass('doc')) {
				first.next().next().prepend("<div class=\"proofcomment\">" + prev.html() + "</div>");
				prev.remove();
				prev = $(this).prev();
				if(prev.hasClass('code')) {
					prev.append($(this).contents());
					$(this).remove();
				}
			}
		}
	});
	$('div.proof').each(function() {
		$(this).css('display', 'none');
		var next = $(this).next();
		while(next.prop('tagName') === 'A' && next.hasClass('proof')) {
			next.remove();
			$(this).next().remove(); // <br />
			next = $(this).next(); // <div class="proof">
			if(!$(next.children()[0]).hasClass('proofcomment')) {
				$(this).append('<hr />');
			}
			$(this).append(next.contents());
			next.remove();
			next = $(this).next();
		}
	});
	$('a.proof').click(function(e) {
		e.preventDefault();
		var proof = $(this).next().next();
		$(this).text((proof.css('display') === 'none' ? 'Hide' : 'Show') + ' proof.');
		proof.slideToggle();
	});
});
