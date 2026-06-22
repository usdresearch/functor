local function strip_outer_paragraph(html)
  html = html:gsub('^<p>', '')
  html = html:gsub('</p>%s*$', '')
  return html
end

local function normalize_latex_math(text)
  text = text:gsub('\\xleftarrow%s*{([^{}]*)}', '\\overset{%1}{\\leftarrow}')
  text = text:gsub('\\xrightarrow%s*{([^{}]*)}', '\\overset{%1}{\\rightarrow}')
  return text
end

local function latex_fragment(elem)
  local text = normalize_latex_math(elem.text)

  if elem.mathtype == 'DisplayMath' then
    return '\\[' .. text .. '\\]'
  end

  return '$' .. text .. '$'
end

function Math(elem)
  local html = pandoc.pipe('pandoc', {
    '--from=latex',
    '--to=html5',
    '--mathml',
  }, latex_fragment(elem))

  return pandoc.RawInline('html', strip_outer_paragraph(html))
end
